
import copy
from inspect import getfullargspec
from lark import Transformer, v_args, Tree, Lark
import hashlib
# import os.path
import os
import json
from traceback import format_stack
import re
import random



depth = 0

len_check = re.compile('::lt::((?!::gt::).)*::gt::')
def nonhtmllength(html):
	return len(len_check.sub('',html))




if True:
	def pmultilinelist(lis,context,word):
		def ppri(sj):
			if type(sj) is not list: return context.asStr(sj)
			return context.orange("[")+",".join([ppri(k) for k in sj])+context.orange("]")
		if type(word) is not list: return context.asStr(word)
		return context.orange("|")+",".join([ppri(k) for k in word])+context.orange("|")

	def pmultilinecsv(context,out,indent,lis,head,tail,lamadapt=None,callback=None,delim=","):
		ocontext = context
		if nonhtmllength(head)<context.magic:
			lisrepr = []
			for k in lis:
				if lamadapt!=None:
					word = context.newcolors(lamadapt(k))
					lisrepr.append(k.prepr(context,word=word))
					context = context.addbits(word)
				else: lisrepr.append(k.prepr(context))
			comb = delim.join(lisrepr)
			if nonhtmllength(head+comb+tail)<context.magic:
				if callback == None:
					out.append("\t"*indent+head+comb+tail)
				else:
					callback(context,out,head+comb+tail)
				return
		out.append("\t"*indent+head)
		context = ocontext
		for k in range(len(lis)):
			if lamadapt!=None:
				word = context.newcolors(lamadapt(lis[k]))
				lis[k].pmultiline(context,out,indent+1,"",delim if k<len(lis)-1 else "",word=word)
				context = context.addbits(word)
			else:
				lis[k].pmultiline(context,out,indent+1,"",delim if k<len(lis)-1 else "")
		if callback == None:
			out.append("\t"*indent+tail)
		else:
			callback(context,out,tail)


	def transferlines(self,pos):
		# if hasattr(pos,'blame'):
		# 	self.blame = pos.blame
		# else:
		# 	self.blame = format_stack()

		if pos == None:
			self.column = 0
			self.row = 0
		else:
			try:
				self.row = pos.row
				self.column = pos.column
			except:
				self.row = pos.line-1
				self.column = pos.column-1


	def assertstatequal(indesc,pos,one,two):
		if two != None and one != None:
			if not one.compare(two):
				raise TypeMismatch(pos,one,two,indesc)



	def untrim(car,mosh):
		if type(mosh) is not list: return mosh
		assert len(car) == len(mosh)
		l = 0
		ysu = []
		for jk in car.rows:
			if jk.obj == None:
				if type(jk.type) is Strategy: ysu.append(untrim(jk.type.type,mosh[l]))
				else: ysu.append(untrim(jk.type,mosh[l]))
				l+=1
			else: ysu.append(None)
		assert l == len(mosh)
		return ysu
	def conservativeeq(a,b):
		if type(a) is list:
			if type(b) is not list: return False
			if len(a) != len(b): return False
			return all(conservativeeq(a[c],b[c]) for c in range(len(a)))
		return type(b) is not list
	def longcount(jj):
		if type(jj) is DualSubs: return sum(longcount(k.name) for k in jj.rows)
		if type(jj) is list: return sum(longcount(k) for k in jj)
		return 1
	def trimlongcount(car,jj):

		return longcount(untrim(car,jj))
	def striphuman(lim,mosh):
		if type(mosh) is not list: return (lim,lim+1)
		ysu = []
		for jk in mosh:
			nan,lim = striphuman(lim,jk)
			ysu.append(nan)
		return (ysu,lim)




	fonocolls = 0
	fonocollson = 0
	fonodepth = 0
	record = {}
	recordon = {}


	def downdeepverify(ahjs,amt):
		if type(ahjs) is RefTree:
			if ahjs.src!=None: ahjs.src.setSafety(amt)
			ahjs.args.setSafety(amt)
		if type(ahjs) is SubsObject:
			for j in ahjs.subs: j.setSafetyrow(amt)
		if type(ahjs) is DualSubs:
			compen = 0
			if ahjs.src!=None: ahjs.src[0].setSafety(amt)
			for j in ahjs.rows:
				if type(j.type) is Strategy and not ahjs.verified:
					j.type.setSafety(amt+compen)
					if j.obj!=None: j.obj.setSafety(amt+compen+longcount(j.type.args))
				else:
					# print(j)
					j.setSafetyrow(amt+compen)
				if j.name == "*****": break
				compen = compen + longcount(j.name)


		if type(ahjs) is Template:
			ahjs.src.setSafety(amt)
		if type(ahjs) is Lambda:
			ahjs.obj.setSafety(amt+longcount(ahjs.si))
		if type(ahjs) is Strategy:
			ahjs.args.setSafety(amt)
			if ahjs.type!=None: ahjs.type.setSafety(amt+longcount(ahjs.args))
	def updeepverify(ahjs):
		if type(ahjs) is RefTree:
			safe = ahjs.args.getSafety()
			if safe!=None: downdeepverify(ahjs,safe)
			safe = ahjs.src.getSafety()
			if safe!=None: downdeepverify(ahjs,safe)
			return safe
		if type(ahjs) is SubsObject:
			just = None
			for j in ahjs.subs:
				just = j.getSafetyrow()
				if just != None:
					downdeepverify(ahjs,just)
					return just
		if type(ahjs) is DualSubs:
			if not ahjs.verified: return
			just = None
			compen = 0
			for j in ahjs.rows:
				just = j.getSafetyrow()
				if just != None:
					downdeepverify(ahjs,just)
					return just-compen
				if j.name == "*****": break
				compen = compen + longcount(j.name)
		if type(ahjs) is Template:
			a = ahjs.src.getSafety()
			# if a == None: a = ahjs.subs.getSafety()
			if a != None: downdeepverify(ahjs,a)
			return a
		if type(ahjs) is Lambda:
			just = ahjs.obj.getSafety()
			if just != None: return just-longcount(ahjs.si)
		if type(ahjs) is Strategy:
			a = ahjs.args.getSafety()
			if a == None:
				just = ahjs.type.getSafety()
				if just != None: a = just - longcount(ahjs.args)
			if a != None: downdeepverify(ahjs,a)
			return a


	def unify(self):
		invert_op = getattr(self,"getSafety",None)
		if callable(invert_op):
			invert_op()






def _dbgEnter_dpush(self,pushes):
	self.setVerified()
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
	else:
		safe = self.getSafety()
	if safe == None: return
	pushes.conforms(safe)
def _dbgExit_dpush(self,pushes,outp):
	pamt = pushes.lenchange()
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
		outp.setSafetyrow(None if safe == None else safe+pamt)
	else:
		safe = self.getSafety()
		outp.setSafety(None if safe == None else safe+pamt)
		outp.setVerified()
def _dbgEnter_ddpush(self,amt,lim,repls,replsrc):
	self.setVerified()
	if type(self) is TypeRow or type(self) is SubRow:
		pass
	else:
		assert lim<=self.verdepth and lim-amt<=self.verdepth
	if repls!=None:
		for k in repls:
			k.setSafety(replsrc)
	assert amt<0




def _dbgEnter_pmultiline(self,context,out,indent,prepend,postpend,callback):
	if context.context!=None:
		if type(self) is TypeRow or type(self) is SubRow:
			self.setSafetyrow(len(context.context))
		else:
			self.setSafety(len(context.context))




def _dbgExit_ddpush(self,amt,lim,repls,replsrc,outp):
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
		outp.setSafetyrow(None if safe == None else safe+amt)
	else:
		safe = self.getSafety()
		outp.setSafety(None if safe == None else safe+amt)
		outp.setVerified()


def _dbgEnter_addfibration(self,args):
	self.setVerified()
	args.setVerified()
	self.setSafety(args.getSafety()+longcount(args))

def _dbgExit_addfibration(self,args,outp):
	outp.setVerified()
	outp.setSafety(args.getSafety())


def _dbgEnter_addlambdas(self,args):
	self.setVerified()
	args.setVerified()
	self.setSafety(args.getSafety()+longcount(args))

def _dbgExit_addlambdas(self,args,outp):
	outp.setVerified()
	outp.setSafety(args.getSafety())





def _dbgEnter_emptyinst(self,limit,mog,prep):
	if prep!=None:
		prep[0].setVerified()
		prep[0].setSafety(prep[1])
		assert prep[1]<=limit
def _dbgExit_emptyinst(self,limit,mog,prep,ahjs):
	limadd = limit + (longcount(self) if mog == False else 0)
	ahjs.setVerified()
	ahjs.setSafety(limadd)




def _dbgEnter_compare(self,other,odsc,thot,extract,lefpush,rigpush):
	if extract != None:
		assert odsc != None
		for j in extract:
			if j[2]!=False:
				j[1].setSafety(odsc)
	lsum = 0 if lefpush == None else lefpush.lenchange()
	rsum = 0 if rigpush == None else rigpush.lenchange()
	self.setVerified()
	other.setVerified()
	if type(self) is SubRow or type(self) is TypeRow:
		other.getSafetyrow()+rsum == self.getSafetyrow()+lsum#dsc values don't match
	else:
		other.getSafety()+rsum == self.getSafety()+lsum#dsc values don't match

def _dbgExit_compare(self,other,odsc,thot,extract,lefpush,rigpush,ahjs):
	# if not ahjs:
	# 	assert False
	if extract != None:
		assert odsc != None








def _dbgEnter_flatten(self,indesc,mog,assistmog,prep,obj,fillout,then):
	assert indesc.oprows.verified
	indesc.setSafety(0)
	if prep != None:
		prep[0].setVerified()
		prep[0].setSafety(prep[1])
	if obj != None:
		obj.setVerified()
		obj.setSafety(len(indesc))
	if prep!=None:
		assert prep[1]<=len(indesc)#default to ==.
	self.setVerified()
	self.setSafety(indesc.beginlen())#tried to flatten something not slotted for beginninglen.
def _dbgExit_flatten(self,indesc,mog,assistmog,prep,obj,fillout,then,ahjs):
	if fillout == None:
		if then: ahjs,asdfasdf = ahjs
		passlen = 0 if prep==None else longcount(prep[0])
		ahjs.setSafety(len(indesc)-passlen)
		# if obj != None and (obj.row!=0 or obj.column!=0):
		# 	for k in ahjs.flat:
		# 		assert k.obj.row!=0 or k.obj.column!=0



def _dbgEnter_addexob(self,exob):
	assert len(exob.subs) != 0
	self.setVerified()
	exob.setVerified()
	exob.setSafety(self.getSafety())#exob is not slotted for indesc(end) in verify

def _dbgExit_addexob(self,exob,outp):
	outp.setSafety(self.getSafety())

def _dbgEnter_verify(self,indesc,carry,reqtype,then):
	# if reqtype: assert not self.verified

	indesc.setSafety(0)
	self.setSafety(indesc.beginlen())#self is not slotted for indesc(begin) in verify
	if carry != None:
		carry.setVerified()
		carry.setSafety(len(indesc))#carry is not slotted for indesc(end) in verify

	assert self.verified == indesc.oprows.verified
	if reqtype:
		assert not self.verified


	if type(self) is RefTree and self.src==None and len(indesc.flat):
		if type(self.name) is int and hasattr(self,'debugname'):
			newname = indesc.flat[indesc.prepushes.translate(self.name)]
			if newname.name != self.debugname and newname.name!=None and self.debugname!=None:
				print("DISCREPANCY")
				print("\t",self.debugname)
				print("\t",newname.name)
				if newname.name=="x": assert False


def _dbgExit_verify(self,indesc,carry,reqtype,then,outp):

	if reqtype:
		outp,natype = outp
		natype.setSafety(len(indesc))
	elif then:
		outp,ninds = outp
		ninds.setSafety(0)
	outp.setVerified()
	outp.setSafety(len(indesc))
	if type(outp) is RefTree and outp.src==None and len(indesc.flat):
		outp.debugname = indesc.flat[(-indesc.postpushes).translate(outp.name)].name



def htmlformat(struct,context,prepend,postpend="",tabs=0,forbidrange=None):
	a = []
	struct.pmultiline(FormatterObject(context,forhtml=True,forbidrange=forbidrange),a,tabs,prepend,postpend)
	return "<br>".join([j.replace("\t","&nbsp;&nbsp;&nbsp;&nbsp;").replace("<","&lt;").replace(">","&gt;").replace("::lt::","<").replace("::gt::",">") for j in a])

class TrackerError(Exception):
	pass


class DDpushError(Exception):
	pass
class DpushError(Exception):
	pass
class PreverifyError(Exception):
	pass



class LanguageError(Exception):
	def __init__(self,pos,message):
		Exception.__init__(self, message + " " + repr(pos))
		# self.blame = 
		self.pos = pos
		self.message = message
		transferlines(self,pos)
		self.soft = None
		self.choices = []
		self.callpattern = None
		self.argdata = None
	def innermessage(self):
		return self.message
	def name(self):
		return "Language Error"
	def hiddenrange(self):
		return ScopeDelta([] if self.argdata==None else [(-self.argdata[2],len(self.argdata[4])-self.argdata[2])])
	def paramhtml(self):
		# def namefromSI(si,car,trail): repr(yoks)+"<br>"+repr(trail)+
		# 	if type(si) is not list:
		yoks,trail,lentho,rowtype,context = self.argdata
		trimmy = context.trimabsolute(lentho)
		message = "<div style='background-color:#4F99A5;border-radius:5px;margin-bottom:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>Inside Parameter "+repr(trail)+":</div><div style='background-color:#39595B;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
		for yok in sorted(yoks,key=lambda x:x[0]):
			if yok[2]==False:
				assert False
				message += htmlformat(yok[1],trimmy.acceptedlist(),str(yok[0])+" = ")+"<br>"
			else:
				message += htmlformat(yok[1],trimmy,str(yok[0])+" = ")+"<br>"
			if type(yok[2]) is not bool: message += "<div style='background-color:#426d70'>"+htmlformat(yok[2],trimmy,"Computed type:",tabs=1)+"</div>"
			if len(yok)>3: message += "<div style='background-color:#426d70'>&nbsp;&nbsp;&nbsp;&nbsp;(assumed from "+str(yok[3])+" parameter.)</div>"
		if rowtype!=None: message += htmlformat(rowtype,context,"Expected Type: ",forbidrange=ScopeDelta([(-lentho,len(context)-lentho)]))
		return message + "</div></div>"
		# return message
	def errorhtml(self):
		message = ""
		if self.argdata!=None: message+=self.paramhtml()
		message += "<div style='background-color:#9A274E;border-radius:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>"+self.name()+":</div><div style='background-color:#612839;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
		message += self.innermessage()
		return message + "</div></div>"
	def tohtml(self):
		choices = []
		callpattern = None

		# if self.row==0 and self.column==0:
		# 	print("IF POS IS MISSING: ")
		# 	print(''.join(self.blame))
		# 	assert False


		for choice in range(len(self.choices)):
			name,row,cr,indesc,error = self.choices[choice]
			pushedrow = row.dpush(ScopeDelta([(len(indesc)-cr,   min(cr,len(indesc))  )]))


			formatted = htmlformat(pushedrow,indesc,name+":")
			if choice==self.callpattern:
				callpattern = formatted
			else:
				choices.append((formatted,error))

		message = ""
		for k in choices:
			message += "<div style='background-color:#8969C3;border-radius:5px;margin-bottom:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>Alternate interpretation:</div><div style='background-color:#594973;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
			message += k[0]
			if k[1]==None:
				message += "<div>Possibility not considered; parameters matched earlier possibility already.</div>"
			else:
				message += "<div>Disregarded Because:</div>"
				message += k[1].errorhtml()
			message += "</div></div>"
		if callpattern != None:
			message += "<div style='background-color:#4F99A5;border-radius:5px;margin-bottom:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>Inside function call:</div><div style='background-color:#39595B;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
			message += callpattern
			message += "</div></div>"
		message += self.errorhtml()
		return message
	def soften(self,shouldsoft):
		self.soft = shouldsoft
		return self
	def callingcontext(self,choices,thispattern):
		if self.callpattern!=None: return self
		self.callpattern = thispattern
		self.choices = choices
		return self
	def addparameterdata(self,yoks,trail,lentho,rowtype,context):
		# def _dbgEnter():
		# 	for yok in yoks:

		if self.callpattern==None and self.argdata!=None: return self
		if self.argdata==None and self.callpattern==None:
			self.argdata = (yoks,trail,lentho,rowtype,context)
		return self



class NonUnionTypeError(LanguageError):
	def __init__(self,pos,expected,context):
		LanguageError.__init__(self,pos,"Objects of the form (a,b) must only be supplied to types of the form {A,B}.")
		self.expected=expected
		self.context=context
	def innermessage(self):
		return self.message+"<br>"+htmlformat(self.expected,self.context,"Expected type: ",forbidrange=self.hiddenrange())
	def name(self):
		return "Type mismatch error"

class NonLambdaTypeError(LanguageError):
	def __init__(self,pos,expected,context):
		LanguageError.__init__(self,pos,"Objects of the form |c|d must only be supplied to types of the form [C]D.")
		self.expected=expected
		self.context=context
	def innermessage(self):
		return self.message+"<br>"+htmlformat(self.expected,self.context,"Expected type: ",forbidrange=self.hiddenrange())
	def name(self):
		return "Type mismatch error"

class TypeRequiredError(LanguageError):
	def __init__(self,pos,lam):
		LanguageError.__init__(self,pos,"Objects of the form "+("|c|d" if lam else "(a,b)")+" require an expected type.")
	def name(self):
		return "Type assumption error"

class TypeMismatch(LanguageError):
	def __init__(self,pos,expected,got,context):
		LanguageError.__init__(self,pos,"Type mismatch.")
		self.expected=expected
		self.got=got
		self.context=context
		# print("CONSTRUCTED WITH:",context)
	def innermessage(self):
		return htmlformat(self.expected,self.context,"Expected: ",forbidrange=self.hiddenrange())+"<br>"+htmlformat(self.got,self.context,"Got: ",forbidrange=self.hiddenrange())
	def name(self):
		return "Type mismatch"

class InvalidSplit(LanguageError):
	def __init__(self):
		LanguageError.__init__(self,None,"Invalid split pattern.")
	def reblame(self,pos,tt,si,context):
		LanguageError.__init__(self,pos,"Invalid split pattern.")
		self.si = repr(si)
		self.tt = tt
		self.context=context
	def innermessage(self):
		return "Pattern: "+self.si+"<br>"+htmlformat(self.tt,self.context,"Tried to split: ",forbidrange=self.hiddenrange())
	def name(self):
		return "Invalid split pattern"

class CouldNotDeduceType(LanguageError):
	def __init__(self,pos):
		LanguageError.__init__(self,pos,"Could not deduce type of argument.")
	def name(self):
		return "Type assumption error"

class VariableAssignmentError(LanguageError):
	def __init__(self,pos,name):
		LanguageError.__init__(self,pos,"Too many positional arguments" if name==None else "Unexpected keyword argument: " + name)
	def name(self):
		return "Unexpected argument"



class ScopeDelta:
	def __init__(self,pushes=None):
		self.pushes = pushes if pushes !=None else []
	def __add__(self,other):
		return ScopeDelta(self.pushes+other.pushes)
	def __sub__(self,other):
		return self+(-other)
	def __neg__(self):
		res = []
		for j in reversed(self.pushes):
			if len(j)==2:
				res.append((-j[0],j[1]))
			else:
				res.append((j[0],j[3],j[2]+j[3]-j[1],j[1]))
		return ScopeDelta(res)
	def __repr__(self):
		return repr(self.pushes)
	def conforms(self,safe):
		for j in self.pushes:
			if len(j)==2:
				assert j[1]<=safe
				assert j[1]-j[0]<=safe
				safe+=j[0]
			else:
				assert j[0]>=0
				assert j[1]>=0
				assert j[2]>=0
				assert j[3]>=0
				assert j[0]+j[1]<=j[2]
				assert j[2]+j[3]<=safe
	def isolate(self):
		return ScopeDelta(copy.copy(self.pushes))
	def isempty(self):
		return len(self.pushes)==0
	def append(self,next):
		self.pushes.append(next)
	def canTranslate(self,fug):
		for j in self.pushes:
			if len(j)==2:
				if fug>=j[1]:
					fug+=j[0]
					if fug<j[1]: return False
			else:
				if   fug>=j[0] and fug<j[0]+j[1]: fug+=j[2]-j[0]
				elif fug>=j[2] and fug<j[2]+j[3]: fug+=j[0]-j[2]
				elif fug>=j[0]+j[1] and fug<j[2]: fug+=j[3]-j[1]
		return True
	def translate(self,fug):
		for j in self.pushes:
			if len(j)==2:
				if fug>=j[1]:
					fug+=j[0]
					if fug<j[1]: raise DpushError()
			else:
				if   fug>=j[0] and fug<j[0]+j[1]: fug+=j[2]-j[0]
				elif fug>=j[2] and fug<j[2]+j[3]: fug+=j[0]-j[2]
				elif fug>=j[0]+j[1] and fug<j[2]: fug+=j[3]-j[1]
		return fug
	def subset(self,fug):
		track = []
		for j in self.pushes:
			assert len(j)==2#safemode
			if fug>j[1]:
				track.append(j)
				fug+=j[0]
				assert fug>=j[1]#safemode
		return ScopeDelta(track)
	def gentlesubset(self,fug):
		track = []
		for j in self.pushes:
			assert j[0]<=0#safemode
			assert len(j)==2#safemode
			if fug>=j[1]-j[0]: track.append(j)
			if fug>=j[1]: fug = max(fug+j[0],j[1])
		return ScopeDelta(track)
	def translateGentle(self,fug):
		return self.gentlesubset(fug).translate(fug)
	def lenchange(self):
		return sum(j[0] for j in self.pushes if len(j)==2)

	def pushchangethru(self,pamt,plim):
		track = []
		for amt,lim in self.pushes:
			if plim>=lim-amt:
				plim+=amt
				track.append((amt,lim))
			else:
				track.append((amt,lim+pamt))
		return ScopeDelta(track)









class FormatterObject:
	def __init__(self,context,magic=60,forhtml=False,forbidrange=None,littleeasier=True,colormap=None):
		self.magic = magic
		self.context = [k.name for k in context.reroll().flat] if type(context) is ScopeObject else context
		self.forhtml = forhtml
		self.forbiddenrange = (forbidrange if forbidrange!=None else ScopeDelta()) - (context.prepushes if type(context) is ScopeObject else ScopeDelta())#[] if forbidrange==None else forbidrange
		self.littleeasier = littleeasier
		self.colormap = {} if colormap==None else colormap

	def getname(self,name):
		if type(name) is str:
			if self.forhtml: return "::lt::span style='color:#fdee73'::gt::"+name+"::lt::/span::gt::"
			return name
		if self.context == None: return str(name)
		if type(name) is int:
			if name in self.colormap and self.forhtml:
				return "::lt::span style='color:"+self.colormap[name]+"'::gt::"+("{no name}" if self.context[name]==None else self.context[name])+"::lt::/span::gt::"
			return self.context[name]

	def red(self,inp):
		if self.forhtml: return "::lt::span style='color:#F92672'::gt::"+inp+"::lt::/span::gt::"
		return inp
	def orange(self,inp):
		if self.forhtml: return "::lt::span style='color:#FD971F'::gt::"+inp+"::lt::/span::gt::"
		return inp
	def addbits(self,nb):
		if self.context==None: return self
		def allbits(bit,canc):
			if type(bit) is list:
				res = []
				for b in bit:
					j,canc = allbits(b,canc)
					res = res+j
				return (res,canc)
			return ([(bit[0],bit[1],canc)],canc+1)
		newbits = allbits(nb,len(self.context))[0]
		return FormatterObject(
			self.context+[k[0] for k in newbits],
			magic=self.magic,
			forhtml=self.forhtml,
			forbidrange=self.forbiddenrange,
			littleeasier=self.littleeasier,
			colormap=dict([kv for kv in list(self.colormap.items())+[(index,color) for name,color,index in newbits]])
		)
	def asStr(self,word):
		if self.forhtml:
			if word[1]==None: return str(word[0])
			return "::lt::span style='color:"+word[1]+"'::gt::"+str(word[0])+"::lt::/span::gt::"
		else: return word[0]

	# def striphuman(lim,mosh):
	# 	if type(mosh) is not list: return (lim,lim+1)
	# 	ysu = []
	# 	for jk in mosh:
	# 		nan,lim = striphuman(lim,jk)
	# 		ysu.append(nan)
	# 	return (ysu,lim)

	def randomcolor(self):
		def hsv_to_rgb(h, s, v):
			if s == 0.0: return (v, v, v)
			i = int(h*6.) # XXX assume int() truncates!
			f = (h*6.)-i; p,q,t = v*(1.-s), v*(1.-s*f), v*(1.-s*(1.-f)); i%=6
			if i == 0: return (v, t, p)
			if i == 1: return (q, v, p)
			if i == 2: return (p, v, t)
			if i == 3: return (p, q, v)
			if i == 4: return (t, p, v)
			if i == 5: return (v, p, q)
		def clamp(x): 
			return max(0, min(int(x*255), 255))
		r,g,b = hsv_to_rgb(random.uniform(80/360.0,280.0/360.0),.7,1)
		return "#{0:02x}{1:02x}{2:02x}".format(clamp(r),clamp(g),clamp(b))
		


	def newcolors(self,si):
		def allbits(si):
			if type(si) is list: return [allbits(b) for b in si]
			# assert si==None or type(si) is str
			return (si,self.randomcolor())
		return allbits(si)


def compose(mapone,maptwo):
	if type(mapone) is list: return [compose(i,maptwo) for i in mapone]
	return maptwo[mapone]
def noneiflatten(map):
	if type(map) is list: return [noneiflatten(m) for m in map]
	return None
def buildfrom(si,plat,vdp):
	if type(si) is list:
		return SubsObject([SubRow(None,buildfrom(m,plat,vdp)) for m in si],verdepth=vdp)
	return plat.flat[si].dpush(ScopeDelta([(-si,vdp)]))
def extfind(h,si,lc=0):
	if type(si) is list:
		for k in si:
			u,lc = extfind(h,k,lc)
			if u!=None: return (u,None)
		return (None,lc)
	if si==h: return (lc,None)
	return (None,lc+1)

#<><><><><>needrowtypes could be false and object is provided............ but there should be objects anyway inherent in the thing you're adding and they need to be subbed with the object that you supplied



def implicitcast(indesc,expected,provided,obj,blame=None,soften=False,extract=None,thot=None,odsc=None,owner=None):
	if expected==None: return obj

	mask = indesc.reroll()

	if extract!=None: st = len(extract)
	eA = 0
	headE = expected
	while headE!=None:
		pA = 0
		headP = provided
		while headP!=None:
			if headE.compare(headP,odsc,thot,extract):
				if extract!=None:
					for kt in range(st,len(extract)): extract[kt] = (extract[kt][0],extract[kt][1],extract[kt][2],owner)

				provob = obj
				if pA>0:
					pp,obk = provided.src
					for p in range(1,pA):
						pp,obi = pp.src
						obk = compose(obk,obi)#<><> order might be flipped here...
						pp=opp
					#turn off needrowtypes once you get that bug figured out<><><><><>
					provob = buildfrom(obk,provided.flatten(mask,[None]*len(provided.rows),obj=provob,needrowtypes=True),provob.verdepth)

				if eA==0: return provob
				# print("beginning expected-side evaluation")

				pp,obk = expected.src
				for e in range(1,eA):
					pp,obi = pp.src
					obk = compose(obk,obi)#<><> order might be flipped here...
					pp=opp
				#turn off needrowtypes once you get that bug figured out<><><><><>
				# print("obj: ",obj.prepr(FormatterObject(mask)))
				# print("provob: ",provob.prepr(FormatterObject(mask)))
				# print("obk: ",obk)

				guflat = headE.flatten(mask,noneiflatten(obk),obj=provob,needrowtypes=True)
				valid = True
				finob = []

				# print("guflat: ",guflat)

				moat = mask
				for h in range(len(expected.rows)):
					fou = extfind(h,obk)[0]
					if fou==None:
						valid = False
						break

					inquestion = guflat.flat[fou].obj.dpush(ScopeDelta([(-fou,len(mask))]))
					# print("inquestion: ",inquestion.prepr(FormatterObject(mask)))
					if expected.rows[h].obj==None:
						finob.append(SubRow(None,inquestion))
						moat = moat.addflat(expected.rows[h].type.flatten(moat,expected.rows[h].name,obj=inquestion.dpush(ScopeDelta([(len(moat)-len(mask),len(mask))]))))
					else:
						against = expected.rows[h].obj.verify(moat).dpush(ScopeDelta([(len(mask)-len(moat),len(mask))]))
						# print("compared against: ",against.prepr(FormatterObject(mask)))
						if not against.compare(inquestion,odsc,thot,extract):#<><><> make sure you aren't comparing things where they're set on both sides- that would be unesscesary.
							valid = False
							break
						moat = moat.addflat(expected.rows[h].type.flatten(moat,expected.rows[h].name,obj=expected.rows[h].obj))



				if valid:
					# print("it's valid")
					return SubsObject(finob,verdepth=provob.verdepth)
			if extract!=None:
				while st<len(extract): del extract[st]

			# if type(headP) is DualSubs and type(headE) is DualSubs and headP.src!=None:
			# 	print("CONDITION 1 SATISFIED")
			# if type(headE) is DualSubs and type(headE) is DualSubs and headE.src!=None:
			# 	print("CONDITION 2 SATISFIED")
			# 	print(headE.src)

			headP = headP.src[0] if type(headP) is DualSubs and type(headE) is DualSubs and headP.src!=None else None
			pA += 1
		headE = headE.src[0] if type(headE) is DualSubs and type(headE) is DualSubs and headE.src!=None else None
		eA += 1
	raise TypeMismatch(blame,expected,provided,indesc).soften(soften)






class ContextYam:
	def __init__(self,operators=None,dependencies=None,verified=False):
		self.operators = operators
		self.dependencies = dependencies
		self.verified = verified
		# self.lastComputation = lastComputation
		# self.nextComputation = Computation()
	def setverified(self):
		return ContextYam(self.operators,self.dependencies,True)



class ScopeObject:
	def __init__(self,flat=None,prpush=None,popush=None,oprows=None):
		self.oprows     = oprows
		self.prepushes  = ScopeDelta() if prpush == None else prpush
		self.postpushes = ScopeDelta() if popush == None else popush
		self.flat = [] if flat == None else flat
		self.memo = []

		def _dbgTest():
			#make sure there are no switch pushes in self.postpushes.
			assert type(self.postpushes) is ScopeDelta
			assert type(self.prepushes) is ScopeDelta
			assert self.postpushes.translateGentle(len(self.flat)) == len(self)
			assert self.postpushes.translate(len(self.flat)) == len(self)
			assert (-self.prepushes).translate(len(self.flat)) == self.beginlen()
			assert self.prepushes.translate(self.beginlen()) == len(self.flat)

		for k in self.postpushes.pushes:
			assert len(k)==2
			assert k[0]<=0

	def setverified(self):
		return ScopeObject(self.flat,self.prepushes,self.postpushes,self.oprows.setverified(assmus))


	def addflat(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes,self.oprows)
	def invisadd(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
			assert len(ahjs)==len(self)
			assert self.beginlen()+len(newflat.flat)==ahjs.beginlen()
		if len(newflat.flat) == 0: return self
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes+ScopeDelta([(-len(newflat.flat),len(self))]),self.oprows)
	def sneakadd(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		if len(newflat.flat) == 0: return self
		return ScopeObject(self.flat+newflat.flat,self.prepushes+ScopeDelta([(len(newflat.flat),len(self.flat))]),self.postpushes,self.oprows)


	def posterase(self,amt):
		if amt == 0: return self
		return ScopeObject(self.flat,self.prepushes,self.postpushes+ScopeDelta([(amt-len(self),amt)]),self.oprows)
	def preerase(self,amt):
		#examine this more closely...
		if amt == 0: return self
		# return ScopeObject(self.flat,self.prepushes+[(len(self)-amt,self.beginlen()+amt-len(self))],self.postpushes,self.oprows)
		return ScopeObject(self.flat,self.prepushes+ScopeDelta([(amt,len(self.flat)-amt)]),self.postpushes,self.oprows)
	def sneakinsert(self,nflat,fillout):
		def _dbgEnter():
			self.setSafety(0)
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		if len(nflat.flat) == 0: return self
		return ScopeObject(self.flat[:fillout] + nflat.flat + [k.dpush(ScopeDelta([(len(nflat.flat),self.postpushes.translateGentle(fillout))])) for k in self.flat[fillout:]],self.prepushes+ScopeDelta([(len(nflat.flat),fillout)]),self.postpushes.pushchangethru(len(nflat.flat),fillout),self.oprows)


	def setSafety(self,safe):
		return
		for i in range(len(self.flat)):
			cr = self.postpushes.translateGentle(i)
			self.flat[i].setVerified()
			try:
				self.flat[i].setSafetyrow(safe+cr)
			except Exception as u:
				print()
				print(self)
				print(i,cr,self.flat[i].getSafetyrow())
				print()
				raise u
			if safe==0 and self.oprows!=None:
				assert (self.flat[i].type==None)==self.oprows.verified
				if not self.oprows.verified:
					if type(self.flat[i]) is TypeRow and type(self.flat[i].obj) is RefTree and self.flat[i].obj.src==None:
						cr1=(-self.postpushes).translate(self.flat[i].obj.name)
						assert self.flat[i].obj.cold == (self.flat[cr1].obj!=None)




	def trimabsolute(self,amt):
		def _dbgEnter():
			self.setSafety(0)
		def _dbgExit(ahjs):
			assert len(self)-amt == len(ahjs)
			assert self.beginlen() == ahjs.beginlen()
		ahjs = ScopeObject(self.flat[:len(self.flat)-amt],-(-self.prepushes).subset(len(self.flat)-amt),self.postpushes,self.oprows)
		return ahjs


	def prepushPR(self,pushes):
		if pushes.isempty(): return self
		return ScopeObject(self.flat,pushes+self.prepushes,self.postpushes,self.oprows)
		# res.memo = [(pushes+pres,com,res) for pres,com,res in self.memo]
		# return res
	def postpushPO(self,pushes):
		if pushes.isempty(): return self
		return ScopeObject(self.flat,self.prepushes,self.postpushes+pushes,self.oprows)
		# return res


	def beginlen(self):
		return len(self.flat) - self.prepushes.lenchange()
	def __len__(self):
		return len(self.flat) + self.postpushes.lenchange()
	def reroll(self):
		# def _dbgEnter():
			# self.setSafety(0)
		def _dbgExit(ahjs):
			# ahjs.setSafety(0)
			assert len(ahjs) == ahjs.beginlen()
			assert len(ahjs) == len(self)
		databus = [TypeRow(k.name,None,k.obj) for k in self.flat]
		for amt,lim in self.postpushes.pushes:
			databus = databus[:lim]+databus[lim-amt:]
		return ScopeObject(databus,None,None,self.oprows.setverified() if self.oprows!=None else None)
	def acceptedlist(self):
		databus = []
		inrow=0
		outrow=0
		while inrow<len(self.flat):
			if self.prepushes.canTranslate(len(databus)):
				if (-self.prepushes).canTranslate(inrow):
					databus.append(self.flat[inrow].name)
				inrow+=1
			else:
				databus.append(None)
		while len(databus)<self.beginlen():databus.append(None)
		return databus


	def symextract(self,name,subs,carry=None,reqtype=False,safety=None,limiter=None,pos=None,cosafety=None,errorcontext=None):
		def _dbgEnter():
			self.setSafety(0)
			for j in subs:
				assert type(j) is tuple and len(j) == 2
				assert type(j[1]) is tuple and len(j[1]) == 2
				if j[1][1]==False:
					j[1][0].setSafety(self.beginlen())
				else:
					j[1][0].setSafety(len(self))
		errorcontext = [] if errorcontext == None else errorcontext
		def compachelper(row):
			def _dbgExit(ahjs):
				if ahjs != None:
					outp = ahjs
					# if reqtype:
					outp,ty = ahjs
					ty.setSafety(len(self))
					# if pos!=None: assert outp.row!=0 or outp.column!=0
					outp.setVerified()
					outp.setSafety(len(self))

			if row == 0:
				return (RefTree(verdepth=len(self),pos=pos),RefTree(verdepth=len(self),pos=pos))# if reqtype else RefTree(verdepth=len(self),pos=pos)
			cr=self.postpushes.translateGentle(row)
			basevalid = limiter==None and self.postpushes.canTranslate(row)
			# if not basevalid: raise DpushError()


			curr = self.flat[row].type.dpush(ScopeDelta([(len(self)-cr,min(cr,len(self)))]))
			bedoin,cuarg,ntype = curr.extractfibrationSubs(self,subs,minsafety=cosafety if type(name) is str else len(subs),maxsafety=safety,blame=pos)
			# print("-=-=-=-=-=-=-=-")
			# # print(ntype.prepr(FormatterObject()))
			# print(ntype)
			# print(cuarg)
			# print(bedoin)
			# print(curr)
			# print(len(self))
			# print(ntype.detect(ScopeDelta([(-longcount(cuarg),len(self))])))
			ntype = ntype.dpush(ScopeDelta([(-longcount(cuarg),len(self))]))


			# bedoin,cuarg,curr = outp
			# bedoin.setSafety(len(indesc))
			# cuarg.setSafety(len(indesc))
			# assert longcount(bedoin) == longcount(cuarg)
			# curr.setSafety(len(indesc)+longcount(bedoin))


			# ntype = ntype.addfibration(cuarg)
			# indesc = self.addflat(cuarg)
			# cuarg,indesc = bedoin.peelcompactify(self,outflow,then=True,earlyabort=True)


			cold = self.flat[row].obj != None

			# ntype = curr.verify(indesc.reroll(),RefTree(verdepth=len(indesc))).addfibration(cuarg)

			drargs = SubsObject(cuarg.extractbetween(bedoin),verdepth=len(self))
			assert len(drargs.subs) == len(bedoin)

			if basevalid: obj = RefTree(cr,drargs,verdepth=len(self),pos=pos,cold=cold)
			if self.flat[row].obj != None:
				# obj = self.flat[row].obj.dpush(ScopeDelta([(len(self)-cr,min(cr,len(self)))])).verify(self.reroll(),None,exollllllllb=drargs if len(drargs.subs)>0 else None).addalts([obj] if basevalid else [])
				
				yobj = self.flat[row].obj.dpush(ScopeDelta([(len(self)-cr,min(cr,len(self)))]))
				if len(drargs.subs)>0: yobj = yobj.addexob(drargs)
				if basevalid: yobj = yobj.addalts([obj])
				obj = yobj

			transferlines(obj,pos)
			return (obj,ntype)

		if len(self.flat) == 0 or name == 0 and limiter==None:
			return (RefTree(verdepth=len(self),pos=pos),RefTree(verdepth=len(self),pos=pos)) if reqtype else RefTree(verdepth=len(self),pos=pos)

		possib = []
		for row in reversed(range(len(self.flat))):
			if limiter!= None and row<limiter: break
			if self.flat[row].name != name: continue
			if limiter== None and not (-self.prepushes).canTranslate(row): continue
			errorcontext.append((name,self.flat[row].type,self.postpushes.translateGentle(row),self,None))
			possib.append(row)
		mmatch = len(errorcontext)
		for row in possib:
			try:
				outp,comptype = compachelper(row)
			except LanguageError as u:
				mmatch -= 1
				if u.soft and len(possib)!=1:
					errorcontext[mmatch] = (errorcontext[mmatch][0],errorcontext[mmatch][1],errorcontext[mmatch][2],errorcontext[mmatch][3],u)
					continue
				u.callingcontext(errorcontext,mmatch)
				raise u

			outp = implicitcast(self,carry,comptype,outp,blame=pos)
			if reqtype: return (outp,comptype)
			return outp


	def precidence(self,ind):
		for j in range(len(self.oprows.operators)):
			if ind in self.oprows.operators[j][0]:
				return (j,self.oprows.operators[j][1]['associate'])
	def __repr__(self):
		# y = 0
		output = []
		for d in self.flat:
			output.append((d.name if type(d.name) is str else repr(d.name))+("|" if d.obj!=None else ""))
		# for x in range(len(self.flat)):
		# 	g=0
		# 	while g<len(hu):
		# 		if hu[g][1] <= y:
		# 			y += hu[g][0]
		# 			output.append("("+str(hu[g][0])+")")
		# 			del hu[g]
		# 		else: g+=1
		# 	output.append(self.flat[x].name)
		# 	y+=1
		# for g in reversed(range(len(hu))):
		# 	if hu[g][1] >= y:
		# 		y += hu[g][0]
		# 		output.append("("+str(hu[g][0])+")")
		# 		del hu[g]
		# assert not len(hu)
		return repr(output)+repr(self.postpushes)+" -- "+repr(self.prepushes)



def juris(name):
	if type(name) is list: return [juris(x) for x in name]
	return (name,None)

class TypeRow:
	def setVerified(self):
		if self.type != None: self.type.setVerified()
		if self.obj != None: self.obj.setVerified()
	def setSafetyrow(self,safe):
		if self.type != None: self.type.setSafety(safe)
		if self.obj != None: self.obj.setSafety(safe)
	def getSafetyrow(self):
		res = None
		if self.type != None:
			res = self.type.getSafety()
			if self.obj!=None and res!=None:self.obj.setSafety(res)
		if res==None and self.obj!=None:
			res = self.obj.getSafety()
			if self.type!=None and res!=None:self.type.setSafety(res)
		return res
	def nonsilent(self):
		return TypeRow(self.name,self.type,self.obj,{'silent':False,'contractible':False})
	def __init__(self,name,ty,obj=None,silent=None):
		self.name = name
		self.type = ty
		self.obj  = obj
		self.silent = silent
		if type(ty) is Lambda or type(ty) is SubsObject: assert False
		# assert self.type != None or self.obj != None
		assert type(self.type) is not Strategy or self.type.type != None or self.obj != None



	def primToJSON(self):
		return (
			self.name,#"name":
			None if self.type==None else self.type.PJID,#"cent":
			None if self.obj==None  else self.obj.PJID,#"obj":
			self.silent#"silent":
		)



	def toJSON(self):
		return {
			"name":self.name,
			"cent":self.type.toJSON(),
			"obj":None if self.obj==None else self.obj.toJSON(),
			"silent":self.silent
		}

	def ddpush(self,amt,lim,repls=None,replsrc=None):
		return TypeRow(self.name,self.type.ddpush(amt,lim,repls,replsrc),None if self.obj == None else self.obj.ddpush(amt,lim,repls,replsrc),self.silent)
	def detect(self,ranges):
		return self.type.quickdetect(ranges) or self.obj!=None and self.obj.quickdetect(ranges)

	def deepsoftdetect(self,ranges):
		return self.type.deepsoftdetect(ranges) or self.obj!=None and self.obj.deepsoftdetect(ranges)


	def dpush(self,pushes):
		return TypeRow(self.name,None if self.type==None else self.type.dpush(pushes),None if self.obj == None else self.obj.dpush(pushes),self.silent)




	def vershortcut(self,indesc):
		return TypeRow(self.name,self.type.verify(indesc),None if self.obj == None else self.obj.verify(indesc),self.silent)
	def unspool(self):
		return self

	def prepr(self,context,word=None):
		if word==None: word = juris(self.name)
		res = "" if self.name == None else pmultilinelist(self.name,context,word)+":"
		if self.silent!=None and self.silent["silent"]:
			if res=="": res = "?:"
			else: res = res[:-1]+"?:"
		if self.type != None: res = res+self.type.prepr(context)
		if self.obj != None: res = res+" = "+self.obj.prepr(context)
		return res
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None,word=None):
		if word==None: word = juris(self.name)
		def calls(context_,out,prepend):
			if self.obj != None:
				self.obj.pmultiline(context,out,indent,prepend,postpend,callback=callback)
			else:
				if callback == None:
					out.append("\t"*indent+prepend+postpend)
				else:
					callback(context,out,prepend+postpend)
		name = "" if self.name == None else pmultilinelist(self.name,context,word)+":"
		if self.silent!=None and self.silent["silent"]:
			if name=="": name = "?:"
			else: name = name[:-1]+"?:"
		self.type.pmultiline(context,out,indent,prepend+name," = " if self.obj != None else "",calls)
	def __repr__(self):
		return self.prepr(FormatterObject(None))
class SubRow:
	def setVerified(self):
		self.obj.setVerified();
	def setSafetyrow(self,safe):
		self.obj.setSafety(safe)
	def getSafetyrow(self):
		return self.obj.getSafety()



	def primToJSON(self):
		return (
			self.name,#"name":
			self.obj.PJID#"obj":
		)
	def toJSON(self):
		assert self.name==None
		return self.obj.toJSON()

	def __init__(self,name,obj):
		self.name = name
		self.obj  = obj
	def ddpush(self,amt,lim,repls=None,replsrc=None):
		return SubRow(self.name,self.obj.ddpush(amt,lim,repls,replsrc))
	def detect(self,ranges):
		return self.obj.detect(ranges)
	def dpush(self,pushes):
		return SubRow(self.name,self.obj.dpush(pushes))

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		return self.obj.compare(other.obj,odsc,thot,extract,lefpush,rigpush)
	def prepr(self,context):
		res = "" if self.name == None or context!=None else pmultilinelist(self.name,context,juris(self.name))+" = "
		res = res+self.obj.prepr(context)
		return res
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		name = "" if self.name == None else pmultilinelist(self.name,context,juris(self.name))+" = "
		self.obj.pmultiline(context,out,indent,prepend+name,postpend,callback)
	def __repr__(self):

		return self.prepr(FormatterObject(None))
class Tobj:
	def setVerified(self):
		assert self.verified
		assert self.verdepth!=None
		pass
	def setSafety(self,safe):
		if safe == None: return
		if hasattr(self,'foclnsafety'): assert self.foclnsafety == safe
		else:
			self.foclnsafety = safe
			downdeepverify(self,safe)
	def getSafety(self):
		if hasattr(self,'foclnsafety'): return self.foclnsafety
		else:
			safe = updeepverify(self)
			if safe != None: self.foclnsafety = safe
			return safe
	def quickdetect(self,ranges):
		for touch in self.touches:
			if not ranges.canTranslate(touch): return self.detect(ranges)
		return False
	def softdetect(self,ranges):
		for touch in self.softtouches:
			if not ranges.canTranslate(touch): return True
		return False
	def deepsoftdetect(self,ranges):
		if self.softdetect(ranges): return True
		for alt in self.altversion:
			if alt.deepsoftdetect(ranges): return True
		return False


	def fibrationalt(self,args):
		vers = []
		for ver in self.altversion:
			try: vers.append(ver.addfibration(args))
			except DpushError: vers = vers + ver.fibrationalt(args)
		return vers


	def ddpushalt(self,amt,lim,repls,replsrc):
		vers = []
		for ver in self.altversion:
			if ver.softdetect(ScopeDelta([(-amt,lim)])): vers = vers+ver.ddpushalt(amt,lim,repls,replsrc)
			else: 
				try: vers.append(ver.ddpush(amt,lim,repls=repls,replsrc=replsrc))
				except DDpushError: vers = vers+ver.ddpushalt(amt,lim,repls,replsrc)
		return vers
	def dpushalt(self,pushes):
		vers = []
		for ver in self.altversion:
			if ver.softdetect(pushes): vers = vers+ver.dpushalt(pushes)
			else: vers.append(ver.dpush(pushes))
		return vers
	def verifyalt(self,indesc,carry):
		vers = []
		for ver in self.altversion:
			if ver.softdetect(indesc.prepushes+indesc.postpushes): vers = vers+ver.verifyalt(indesc,carry)
			else: vers.append(ver.verify(indesc,carry))
		return vers
	def addalts(self,alts):
		def _dbgEnter():
			for alt in alts: alt.setSafety(self.getSafety())

		if not len(alts):return self
		cop = copy.copy(self)
		cop.touches = copy.copy(cop.touches)
		
		cop.altversion = cop.altversion + alts
		for alt in alts:
			cop.touches.update(alt.touches)
			if alt.softtouches == cop.softtouches:
				assert False
		for n in range(len(cop.altversion)):
			for m in range(n):
				if n!=m and cop.altversion[n].softtouches==cop.altversion[m].softtouches:
					print(cop.altversion[n].softtouches)
					print(self.altversion)
					print(alts)
					assert False
		return cop


	def flatten(self,indesc,mog,assistmog=None,prep=None,obj=None,fillout=None,then=False,needrowtypes=False):
		if not needrowtypes: return ScopeObject([TypeRow(mog,None,obj)])
		if type(mog) is list: raise InvalidSplit(None)
		if prep != None: njprep = prep[0].dpush(ScopeDelta([(len(indesc)-longcount(prep[0])-prep[1],prep[1])]))
		if prep == None or len(njprep.rows)==0:
			return ScopeObject([TypeRow(mog,self.verify(indesc),None if obj == None else obj)])
		else:
			spap = len(indesc)-longcount(njprep)

			t1 = self.verify(indesc).addfibration(njprep)

			t2 = None if obj == None else obj.addlambdas(njprep)

			return ScopeObject([TypeRow(mog,t1,t2)])
	def isemptyinst(self,si,prep=None):
		return False
	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not int: raise InvalidSplit()
		prep = None if prep == None else prep[0].dpush(ScopeDelta([(limit-prep[1],prep[1])]))

		return RefTree(name=mog,args=prep,verdepth=limit)
	def addfibration(self,args):
		shaz = longcount(args)
		if len(args) == 0:
			return self.dpush(ScopeDelta([(-shaz,self.verdepth-shaz)]))
		return Strategy(args,self,verdepth=self.verdepth-shaz,pos=self,altversion=self.fibrationalt(args))
	def addlambdas(self,args,pos=None):
		starter = self.verdepth-longcount(args)
		si = args.semavail()
		disgrace = ScopeDelta()
		largs = args.trimallnonessential(si,disgrace=disgrace)
		return (self.dpush(disgrace) if not disgrace.isempty() else self).addlambdasphase2(si,pos=pos)
	def addlambdasphase2(self,si,pos=None):
		if len(si)==0: return self
		elim=0
		fafter = self.verdepth
		starter = fafter-longcount(si)
		outp = self
		if type(self) is RefTree and self.name<starter:
			elim=0
			while elim<len(si) and elim<len(self.args.subs):
				ndepth = starter+longcount(si[:len(si)-elim-1])
				thisdepth = longcount(si[len(si)-elim-1])
				valid = True
				for k in self.args.subs[:len(self.args.subs)-1-elim]:
					if k.obj.quickdetect(ScopeDelta([(-thisdepth,ndepth)])):
						valid = False
						break
				if not valid: break
				# purecomponent = largs.rows[len(largs.rows)-1-elim].type.emptyinst(fafter,striphuman(ndepth,si[len(si)-1-elim])[0])
				# if not self.args.subs[len(self.args.subs)-1-elim].obj.compare(purecomponent): break
				# purecomponent = largs.rows[len(largs.rows)-1-elim].type.emptyinst(fafter,striphuman(ndepth,si[len(si)-1-elim])[0])
				if not self.args.subs[len(self.args.subs)-1-elim].obj.isemptyinst(striphuman(ndepth,si[len(si)-1-elim])[0]): break
				elim+=1
			if elim:
				ndepth = starter+longcount(si[:len(si)-elim])
				nsubs = SubsObject([k.dpush(ScopeDelta([(ndepth-fafter,ndepth)])) for k in self.args.subs[:len(self.args.subs)-elim]],verdepth=ndepth)
				outp = RefTree(self.name,nsubs,None if self.src==None else self.src.dpush(ScopeDelta([(ndepth-fafter,ndepth)])),verdepth=ndepth,cold=self.cold,pos=self)
		if type(self) is Lambda:
			return Lambda(si[:len(si)-elim]+self.si,self.obj,verdepth=starter,altversion=[al.addlambdasphase2(si) for al in self.altversion],pos=self if pos==None else pos)
		if len(si)==elim: return outp
		return Lambda(si[:len(si)-elim],outp,verdepth=starter,pos=self if pos==None else pos)
	def extractfibration(self,indesc,si,blame=None):
		if len(si)==0: return (DualSubs(verdepth=self.verdepth),self)
		try:
			carry = self.trimallnonessential(si) if type(self) is Strategy else self
		except InvalidSplit as u:
			u.reblame(blame,self.args,si,indesc)
			raise u

		alts = []
		ac = []
		while len(si)>len(ac):

			if type(carry) is RefTree:
				mogo = carry.mangle_FE()
				if mogo!=None: carry = mogo
			if type(carry) is not Strategy: raise NonLambdaTypeError(blame,self,indesc)

			# preserve alts on mangle?
			for k in carry.altversion: alts.append(k.addfibration(DualSubs(ac,verdepth=self.verdepth)))

			ac = ac + carry.args.rows
			carry = carry.type

		advdepth = self.verdepth+longcount([a.name for a in ac[:len(si)]])
		if len(si)<len(ac):
			if type(carry) is Strategy:
				carry = Strategy(DualSubs(ac[len(si):]+carry.args,verdepth=advdepth),carry.type,verdepth=advdepth,pos=carry)
				ac = ac[:len(si)]
			else:
				carry = Strategy(DualSubs(ac[len(si):],verdepth=advdepth),carry,verdepth=advdepth,pos=carry)
				ac = ac[:len(si)]

		subalts = []
		for k in alts:
			try: subalts.append(k.extractfibration(indesc,si,blame=blame)[1])
			except NonLambdaTypeError as u: pass
			except VariableAssignmentError as u: pass

		return (DualSubs(ac,verdepth=self.verdepth),carry.addalts(subalts))

	def extractfibrationSubs(self,indesc,si,minsafety=None,maxsafety=None,blame=None):
		# def _dbgExit(outp):
		# 	bedoin,cuarg,curr = outp
		# 	bedoin.setSafety(len(indesc))
		# 	cuarg.setSafety(len(indesc))
		# 	assert longcount(bedoin) == longcount(cuarg)
		# 	curr.setSafety(len(indesc)+longcount(bedoin))
		# 	assert not curr.detect(ScopeDelta([(-longcount(cuarg),len(indesc))]))

		if len(si)==0: return (DualSubs(verdepth=self.verdepth),DualSubs(verdepth=self.verdepth),self)
		try:
			carry = self.trimallnonessential() if type(self) is Strategy else self
		except InvalidSplit as u:
			u.reblame(blame,self.args,si,indesc)
			raise u
		nindesc = indesc
		inflow = si
		alts = []
		ac = []
		dc = []
		earlyabort = True
		while len(inflow):
			assert not carry.detect(ScopeDelta([(-longcount([a.name for a in ac]),len(indesc))]))

			if type(carry) is RefTree:
				mogo = carry.mangle_FE()
				if mogo!=None: carry = mogo
			if type(carry) is not Strategy:
				raise VariableAssignmentError(blame,inflow[0][0])
			# preserve alts on mangle?
			for k in carry.altversion: alts.append(k.addfibration(DualSubs(ac,verdepth=self.verdepth)))

			oflow = []

			(dbdbdb,earlyabort),nindesc = carry.args.peelcompactify(nindesc,carry.args.compacassign(inflow,oflow,minsafety,maxsafety),then=True,earlyabort=earlyabort)
			if any(k.obj==None for k in dc): raise LanguageError(blame,"Hole in arguments list")

			if minsafety!=None: minsafety -= len(carry.args.rows)
			if maxsafety!=None: maxsafety -= len(carry.args.rows)
			gc = longcount(carry.args)
			pob = ScopeDelta([(gc,len(nindesc)-gc)])
			# nindesc = nindesc.prepushPR(pob)

			inflow = [(o[0],(o[1][0] if o[1][1]==False else o[1][0].dpush(pob),o[1][1] if type(o[1][1]) is bool else o[1][1].dpush(pob))) for o in oflow]

			ac = ac + carry.args.rows
			dc = dc + dbdbdb.rows
			carry = carry.type.verify(nindesc.reroll())


		lensi = 0
		while lensi<len(dc) and dc[lensi].obj!=None:lensi+=1



		advdepth = self.verdepth+longcount([a.name for a in ac[:lensi]])
		if lensi<len(ac):
			if type(carry) is Strategy:
				carry = Strategy(DualSubs(dc[lensi:]+carry.args,verdepth=advdepth),carry.type,verdepth=advdepth,pos=carry)
			else:
				carry = Strategy(DualSubs(dc[lensi:],verdepth=advdepth),carry,verdepth=advdepth,pos=carry)
			ac = ac[:lensi]
			dc = dc[:lensi]

		# print(lensi,len(ac),len(dc))
		# print(carry)
		# print(ac)
		# print(dc)
		# assert not carry.detect(ScopeDelta([(-longcount([a.name for a in ac]),len(indesc))]))

		subalts = []
		for k in alts:
			try: subalts.append(k.extractfibrationSubs(indesc,si,blame=blame)[2])
			except NonLambdaTypeError as u: pass
			except VariableAssignmentError as u: pass

		# if any(k.obj==None for k in dc): raise LanguageError(blame,"Hole in arguments list")

		# print(nindesc)
		return (DualSubs(ac,verdepth=self.verdepth),DualSubs(dc,verdepth=self.verdepth),carry.addalts(subalts))





	def reference(self,s):
		if type(self) is SubsObject: return self.subs[s].obj
		elif type(self) is Lambda and type(self.obj) is SubsObject: return Lambda(self.si,self.obj.subs[s].obj,verdepth=self.verdepth,pos=self)
		else: return RefTree(src=self,name=s,verdepth=self.verdepth,pos=self)


	def unspool(self):
		return self
		pass
	def __repr__(self):
		return self.prepr(FormatterObject(None))



def altPmultiline(F):
	def wrapper(self,context,out,*args,**kwargs):
		if context.context==None:
			F(self,context,out,*args,**kwargs)
			return
		complete = []
		thissucks = self.altversion
		u = 0
		while u<len(thissucks):
			a = thissucks[u]
			u+=1
			if a.softdetect(context.forbiddenrange):
				thissucks = thissucks + a.altversion
				continue
			complete.append([])
			a.pmultiline(context,complete[-1],*args,**kwargs)
		if len(complete):
			m = complete[0]
			for a in complete[1:]:
				if sum([len(b) for b in a])<sum([len(b) for b in m]):
					m = a
			for j in m: out.append(j)
		else:
			F(self,context,out,*args,**kwargs)
	return wrapper





def altPrepr(F):
	def wrapper(self,context,*args,**kwargs):
		if context.context!=None:
			complete = []
			thissucks = self.altversion
			u = 0
			while u<len(thissucks):
				a = thissucks[u]
				u+=1
				if a.softdetect(context.forbiddenrange):
					thissucks = thissucks + a.altversion
					continue
				complete.append(a.prepr(context,*args,**kwargs))
			if len(complete):
				m = complete[0]
				for a in complete[1:]:
					if len(a)<len(m): m = a
				return m
		return F(self,context,*args,**kwargs)
	return wrapper


def initTobj(F):
	def wrapper(self,*args,pos=None,verified=True,altversion=None,**kwargs):
		"""dbg_ignore"""
		# if 'src' not in kwargs: pos = None
		transferlines(self,pos)

		self.verified = verified
		self.altversion = [] if altversion==None else altversion
		self.verdepth = None
		self.complexity = 0
		self.PJID = None
		F(self,*args,**kwargs)
		if "verdepth" in kwargs:
			# assert self.verdepth!=-60
			for alt in self.altversion: alt.setSafety(kwargs.get("verdepth"))
			self.setSafety(kwargs.get("verdepth"))
			for k in self.touches:
				assert k==0 or k<self.verdepth
			for alt in self.altversion:
				# assert type(alt) is RefTree and alt.src==None#safemode
				self.touches.update(alt.touches)
				if alt.softtouches==self.softtouches:
					assert False
		# else:
		# 	assert self.row!=0 or self.column!=0
		# if repr(self) == '114(120,118,119,123,121)': assert False
		# if repr(self) ==                                                  '116(134,133,114(134,132,133,137,135))': raise TrackerError()
		# if repr(self) == '|a,b,c,q1,q2|11(104(118,120),103(120,118),|s|122(116(120,119,114(120,118,119,123,121)),104(118,120)),|s|123)': raise TrackerError()
		# 									|a,b,c,q1,q2|11(103(117,119),102(119,117),|s|121(115(119,118,113(119,117,118,122,120)),103(117,119)),|s|122)

	return wrapper

def lazyverify(F):
	def wrapper(self,indesc,carry=None,reqtype=False,then=False):
		"""dbg_ignore"""
		if not indesc.oprows.verified or then:
			return F(self,indesc,carry,reqtype,then)
		for touch in self.touches:
			if touch!=0 and indesc.flat[indesc.prepushes.translate(touch)].obj!=None:
				return F(self,indesc,carry,reqtype,then)
		if not indesc.prepushes.isempty() or not indesc.postpushes.isempty():
			return self.dpush(indesc.prepushes+indesc.postpushes)
		return self
	return wrapper

def lazydpush(F):
	return F

def flattenunravel(si,ob=None,left=0):
	if type(si) is list:
		res = []
		for n in range(len(si)):
			res = res + flattenunravel(si[n],ob.reference(n) if ob!=None else None,left+len(res))
		return res
	return [TypeRow(si,None,None if ob == None or left==None else ob.dpush(ScopeDelta([(left,ob.verdepth)])))]


def lazyflatten(F):
	def wrapper(self,indesc,mog=False,assistmog=None,prep=None,obj=None,fillout=None,then=False,needrowtypes=False):
		"""dbg_ignore"""

		sel = self if type(self) is DualSubs else self.type if type(self) is Strategy else None
		if mog == False: mog = sel.fulavail()

		if not needrowtypes:
			return ScopeObject(flattenunravel(mog,obj))

		if type(mog) is not list: return Tobj.flatten(self,indesc,mog,assistmog,prep,obj,fillout=fillout,needrowtypes=needrowtypes)
		if len(sel.fulavail()) != len(mog):
			raise InvalidSplit()
		if assistmog == None:
			assistmog,ext = striphuman(len(indesc),mog)
			fillout = len(indesc.flat)

		return F(self,indesc,mog,assistmog,prep,obj,fillout,then)
	return wrapper






class DualSubs(Tobj):
	@initTobj
	def __init__(self,rows=None,verdepth=None,src=None):
		self.rows = rows if rows != None else []
		self.src = src
		if verdepth!=None:
			self.verdepth = verdepth
			self.touches = set()
			self.softtouches = set()
			self.complexity = 1
			for sub in self.rows:
				assert type(sub) is TypeRow#safemode
				self.touches.update(sub.type.touches)
				self.softtouches.update(sub.type.softtouches)
				self.complexity+=sub.type.complexity
				if sub.obj!=None:
					self.touches.update(sub.obj.touches)
					self.softtouches.update(sub.obj.softtouches)
					self.complexity+=sub.obj.complexity
			self.touches = {k for k in self.touches if k<verdepth}
			self.softtouches = {k for k in self.softtouches if k<verdepth}

	def extractbetween(self,older):
		for j in self.rows: assert j.obj != None
		cuu = []
		left = 0
		for g in range(len(self.rows)):
			if older.rows[g].obj == None:
				cuu.append(SubRow(None,self.rows[g].obj.dpush(ScopeDelta([(-left,self.verdepth)]))))
			left += longcount(older.rows[g].name)
		return cuu


	def primToJSON(self):
		return (
			"DualSubs",#"type":
			[k.PJID for k in self.rows]#"rows":
		)
	def toJSON(self):
		return {
			"type":"DualSubs",
			"rows":[k.toJSON() for k in self.rows]
		}
	@altPrepr
	def prepr(self,context):
		yud = []
		for k in self.rows:
			word = context.newcolors(k.name)
			yud.append(k.prepr(context,word=word))
			context = context.addbits(word)
		return context.red("{")+",".join(yud)+context.red("}")
	@altPmultiline
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		pmultilinecsv(context,out,indent,self.rows,prepend+context.red("{"),context.red("}")+postpend,lamadapt=lambda x:x.name,callback=callback,delim=context.red(","))


	def ddpush(self,amt,lim,repls=None,replsrc=None,disgrace=None):
		disgrace = ScopeDelta() if disgrace == None else disgrace
		left = 0
		cu = []
		for k in range(len(self.rows)):
			try:
				m = self.rows[k]
				if not disgrace.isempty(): m = m.dpush(disgrace)
				m = m.ddpush(amt,lim,repls,replsrc)
			except DDpushError as u:
				if self.rows[k].obj == None: raise u
				disgrace.append((-longcount(self.rows[k].name),self.verdepth+left))
			else:
				cu.append(m)
				left += longcount(self.rows[k].name)
		return DualSubs(cu,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc),src=None if self.src==None else (self.src[0].ddpush(amt,lim,repls,replsrc),self.src[1]),pos=self)
	def detect(self,ranges,merge=False):
		if not merge: ranges = ranges.isolate()
		dsc = self.verdepth
		for row in self.rows:
			lc = longcount(row.name)
			if row.detect(ranges):
				if row.obj==None: return True
				ranges.append((-lc,dsc))
			else:
				dsc+=lc
		return False
	def dpush(self,pushes,disgrace=None):
		disgrace = ScopeDelta() if disgrace == None else disgrace
		left = 0
		cu = []
		for k in range(len(self.rows)):
			try:
				m = self.rows[k].dpush(disgrace+pushes)
			except DpushError as u:
				if self.rows[k].obj == None: raise u
				disgrace.append((-longcount(self.rows[k].name),self.verdepth+left))
			else:
				cu.append(m)
				left += longcount(self.rows[k].name)
		return DualSubs(cu,verdepth=None if self.verdepth==None else self.verdepth+pushes.lenchange(),altversion=self.dpushalt(pushes),src=None if self.src==None else (self.src[0].dpush(pushes),self.src[1]),pos=self)

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None,keepr=False,advanced=None):
		if type(other) is RefTree:
			att = other.mangle_UE()
			if att!=None: return self.compare(att,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not DualSubs: return False
		if len(self) == len(other): advanced = None
		if len(self) < len(other) and advanced==None: return False
		if len(self) > len(other): return False
		if lefpush == None: lefpush = ScopeDelta()
		if rigpush == None: rigpush = ScopeDelta()
		if not keepr:
			lefpush = lefpush.isolate()
			rigpush = rigpush.isolate()
		lk = 0
		rk = 0
		dsc = self.verdepth + lefpush.lenchange()
		while lk<len(self.rows) or rk<len(other.rows):
			if lk<len(self.rows) and self.rows[lk].obj != None:
				jl = longcount(self.rows[lk].name)
				lefpush.append((-jl,dsc))
				lk += 1
			if lk==len(self.rows) and advanced!=None:
				while rk<len(other.rows):
					advanced.append(other.rows[rk])
					rk+=1
			if rk<len(other.rows) and other.rows[rk].obj != None:
				jr = longcount(other.rows[rk].name)
				rigpush.append((-jr,dsc))
				rk += 1
			if lk<len(self.rows) and rk<len(other.rows) and self.rows[lk].obj==None and other.rows[rk].obj==None:
				if not conservativeeq(self.rows[lk].name,other.rows[rk].name): return False

				if not self.rows[lk].type.compare(other.rows[rk].type,odsc,thot,extract,lefpush,rigpush): return False
				j = longcount(self.rows[lk].name)
				dsc += j
				lk += 1
				rk += 1
		return True
	def append(self,other):
		return DualSubs(self.rows+[other],verdepth=self.verdepth)
	def __add__(self,other):
		return DualSubs(self.rows+other.rows,verdepth=self.verdepth)
	def __len__(self):
		return len([k for k in self.rows if k.obj == None])
	def __getitem__(self, key):
		return [k for k in self.rows if k.obj == None][key].type
	def fulavail(self):
		return [j.name for j in self.rows]
	def semavail(self,mog=False):
		if mog == False: mog = self.fulavail()
		return [self.rows[k].type.semavail(mog[k]) if type(mog[k]) is list else mog[k] for k in range(len(self.rows)) if self.rows[k].obj == None]
	def trimallnonessential(self,si=None,disgrace=None):
		disgrace = ScopeDelta() if disgrace == None else disgrace
		def unshift(lim,car,old,new):
			if type(old) is not list: return lim+1
			s=0
			for k in range(len(car)):
				row = car[k]
				if row.obj==None:
					if type(new[s]) is list:
						ncar = car.type.type if type(car.type) is Strategy else car.type
						lim = unshift(lim,ncar.rows,old[k],new[s])
					else:
						lim+=longcount(old[k])
					s+=1
				else:
					disgrace.append((-longcount(old[k]),self.verdepth+left))
		left = 0
		cu = []
		si = self.semavail() if si==None else si
		s = 0
		for k in range(len(self.rows)):
			if self.rows[k].obj == None: 
				m = self.rows[k]
				if not disgrace.isempty(): m = m.dpush(disgrace)
				if s<len(si) and type(si[s]) is list:
					if type(m.type) is DualSubs:
						left = unshift(left,m.type.rows,self.rows[k].name,si[s])
						m = TypeRow(m.name,m.type.trimallnonessential(si[s]),m.obj,m.silent)
					elif type(m.type) is Strategy and type(m.type.type) is DualSubs:
						left = unshift(left,m.type.type.rows,self.rows[k].name,si[s])
						m = TypeRow(m.name,Strategy(m.type.args,m.type.type.trimallnonessential(si[s]),verdepth=m.type.verdepth),m.obj,m.silent)
					else: raise InvalidSplit()
				else:
					left += longcount(self.rows[k].name)
				cu.append(m)
				s += 1
			else:
				disgrace.append((-longcount(self.rows[k].name),self.verdepth+left))
		return DualSubs(cu,verdepth=self.verdepth,altversion=self.altversion)
	@lazyflatten
	def flatten(self,indesc,mog,assistmog,prep=None,obj=None,fillout=None,then=False):

		s = 0
		cu = ScopeObject()
		for n in range(len(self.rows)):
			nobj = None
			if self.rows[n].obj != None:
				nobj = self.rows[n].obj.verify(indesc)
			else:
				if obj != None:
					nobj = obj.reference(s)
					if len(indesc)!=obj.verdepth: nobj = nobj.dpush(ScopeDelta([(len(indesc)-obj.verdepth,obj.verdepth)]))
				s+=1
			nflat = self.rows[n].type.flatten(indesc,mog[n],assistmog[n],prep,obj=nobj,fillout=fillout,needrowtypes=True)
			cu.flat += nflat.flat
			if conservativeeq(self.rows[n].name,mog[n]) and prep == None:
				indesc = indesc.addflat(nflat.reroll())
			else:
				indesc1 = indesc.sneakinsert(nflat.reroll(),fillout)
				passprep = (prep[0].emptyinst(len(indesc1),striphuman(len(indesc1)-longcount(prep[0]),prep[0].fulavail())[0]),len(indesc1)) if prep != None else None
				nobj = nobj.dpush(ScopeDelta([(len(indesc1)-len(indesc),len(indesc))])) if nobj != None else self.rows[n].type.emptyinst(len(indesc1),assistmog[n],prep=passprep)#prep is just the actual parameters that need to be prepended.
				oflat = self.rows[n].type.flatten(indesc1,self.rows[n].name,obj=nobj,needrowtypes=False)
				indesc = indesc1.invisadd(oflat)
			fillout = fillout + len(nflat.flat)

		return (cu,indesc) if then else cu
	def emptyinst(self,limit,mog=False,prep=None):
		if mog == False: mog,limit = striphuman(limit,self.fulavail())
		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)
		assert len(self.rows) == len(mog)
		mog = [mog[i] for i in range(len(mog)) if self.rows[i].obj == None]
		return SubsObject([SubRow(None,self[k].emptyinst(limit,mog[k],prep)) for k in range(len(self))],verdepth=limit)
	def needscarry(self):
		return False
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		if not self.verified: assertstatequal(indesc,self,carry,RefTree(verdepth=len(indesc)))
		outs = []
		oidns = indesc
		bi = len(indesc)
		if indesc.oprows.verified:

			for n in range(len(self.rows)):
				nty = self.rows[n].type.verify(indesc,RefTree(verdepth=len(indesc)))
				obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None

				vertype = TypeRow(self.rows[n].name,nty,obj,self.rows[n].silent)
				outs.append(vertype)
				if type(self.rows[n].name) is not list:
					indesc = indesc.addflat(ScopeObject([TypeRow(self.rows[n].name,None,obj)]))
				else: indesc = indesc.addflat(nty.flatten(indesc.reroll(),self.rows[n].name,obj=obj,needrowtypes=not indesc.oprows.verified))

		else:
			for n in range(len(self.rows)):
				if self.rows[n].type == None:
					obj,nty = self.rows[n].obj.verify(indesc,reqtype=True)
				elif type(self.rows[n].type) is Strategy:

					gnoa,ndsid = self.rows[n].type.args.verify(indesc,then=True)
					if self.rows[n].type.type == None:
						obj,nty = self.rows[n].obj.verify(ndsid,reqtype=True)
					else:
						nty = self.rows[n].type.type.verify(ndsid,RefTree(verdepth=len(ndsid)))
						obj = self.rows[n].obj.verify(ndsid,nty) if self.rows[n].obj!=None else None

					nty = Strategy(gnoa,nty,verdepth=len(indesc))

					if obj!=None:
						despar = ScopeDelta()
						gnoa.trimallnonessential(None,despar)
						if not despar.isempty(): obj = obj.dpush(despar)
						obj = Lambda(gnoa.semavail(),obj,verdepth=len(indesc),pos=obj)
				else:
					nty = self.rows[n].type.verify(indesc,RefTree(verdepth=len(indesc)))
					obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None

				if self.rows[n].name == "*****": self.rows[n].name = nty.fulavail()

				vertype = TypeRow(self.rows[n].name,nty,obj,self.rows[n].silent)
				outs.append(vertype)
				if type(self.rows[n].name) is not list:
					indesc = indesc.addflat(ScopeObject([vertype]))
				else: indesc = indesc.addflat(nty.flatten(indesc.reroll(),self.rows[n].name,obj=obj,needrowtypes=not indesc.oprows.verified))


		outp = DualSubs(outs,pos=self,verdepth=bi,altversion=self.verifyalt(oidns,carry),src=None if self.src==None else (self.src[0].verify(indesc,carry),self.src[1]))
		return (outp,indesc) if then else (outp,RefTree(verdepth=bi)) if reqtype else outp
	def peelcompactify(self,indesc,compyoks,then=False,earlyabort=True):
		def _dbgEnter():
			indesc.setSafety(0)
			assert type(compyoks) is list
			for j in compyoks:
				assert type(j) is tuple and (len(j) == 3 or len(j)==4)
				if j[2]==False:
					j[1].setSafety(indesc.beginlen())
				else:
					j[1].setSafety(len(indesc))
		def _dbgExit(outp):
			if outp != None:
				if then:
					outp,ninds = outp
					assert type(ninds) is ScopeObject
					ninds.setSafety(0)
				outp,early = outp
				assert type(early) is bool
				assert type(outp) is DualSubs
				outp.setVerified()
				outp.setSafety(len(indesc))

		for y in range(len(compyoks)):
			if len(compyoks[y])>3:
				compyoks[y] = (compyoks[y][0],compyoks[y][1],compyoks[y][2])
		return self.compacrecurse(compyoks,[],[],indesc,then=then,earlyabort=earlyabort)




	def compacassign(self,inyoks,overflow=None,cosafety=None,safety=None):
		prev = False
		for g in inyoks:
			if g[0] != None: prev = True
			elif prev: raise LanguageError(self,"positional argument may not follow keyword argument.")
		def firstnamed(spoken,labels,car,mot=None,blame=None,name=None):
			# more prots
			mot = car.fulavail() if mot == None else mot
			for f in range(len(mot)):
				if car.rows[f].obj != None: continue
				if spoken[f] == True: continue
				if isinstance(mot[f],list):
					if spoken[f] == False: spoken[f] = [False]*len(mot[f])
					k = firstnamed(spoken[f],labels,car.rows[f].type,mot[f],blame=blame,name=name)
					if k: return [f] + k
				elif mot[f] == labels[0] or (labels[0] == None and ((cosafety!=None and f<cosafety) or (car.rows[f].silent==None or not car.rows[f].silent['silent']))):
					if len(labels) == 1:
						spoken[f] = True
						return [f]
					nxc = car.rows[f].type.type if type(car.rows[f].type) is Strategy else car.rows[f].type

					if type(car.rows[f].type) is not DualSubs:
						raise LanguageError(blame,"Tried to subaccess thing that doesn't have subproperties "+str(name))

					if spoken[f] == False: spoken[f] = [False]*len(nxc)
					k = firstnamed(spoken[f],labels[1:],nxc)
					if k: return [f]+k
		def fullp(spoken):
			if spoken == False: return False
			return spoken == True or all(fullp(k) for k in spoken)
		spoken = [False]*len(self.rows)
		yoks = []
		for s in range(len(inyoks)):
			nan = firstnamed(spoken,[None] if inyoks[s][0] == None else inyoks[s][0],self,blame=inyoks[s][1][0],name=inyoks[s][0])
			if nan == None:
				if safety != None and s < safety: raise VariableAssignmentError(inyoks[s][1][0],inyoks[s][0])
				overflow.append(inyoks[s])
			else:
				yoks.append((nan,inyoks[s][1][0],inyoks[s][1][1]))
		return yoks
	def compacrecurse(self,yoks,trail,prep,indesc,then=False,earlyabort=False):
		def _dbgEnter():
			indesc.setSafety(0)
			assert type(yoks) is list
			for j in yoks:
				assert type(j) is tuple
				if j[2]==False:
					j[1].setSafety(indesc.beginlen())
				else:
					j[1].setSafety(len(indesc)-len(prep))
			self.setVerified()
			self.setSafety(len(indesc))
			# for c in yoks:
			# 	assert "AUUUAUUAUAUAU" not in repr(c)
		def _dbgExit(outp):
			if len(outp)==4:
				ming,frame,reassembled,earlyabort = outp
				frame.setSafety(0)
				return
			elif then:
				outp,ninds = outp
				assert type(ninds) is ScopeObject
				ninds.setSafety(0)
			outp,early = outp
			assert type(early) is bool
			assert type(outp) is DualSubs
			outp.setVerified()
			outp.setSafety(len(indesc))
			for c in yoks:
				if c[2]==False:
					print(c)
					print(self)
					assert False

		assert not indesc.oprows.verified

		cu = []
		def getming(thot,st):
			ming = None;
			for regrab in yoks[st:len(yoks)]:
				if ming == None:
					ming = regrab[0]
					continue
				for i in range(min(len(ming),len(regrab[0]))):
					if regrab[0][i]<ming[i]:
						ming = regrab[0]
						break
			return ming
		def restart(thot,ming):
			l = 0
			while ming[l]==(trail+[n])[l]: l+=1
			p=0
			while True:
				for i in range(l):
					if thot[p][1][i]!=ming[i]: break
				else: break
			frame = indesc.trimabsolute(lentho-p)
			reassembled = DualSubs(cu + [self.rows[b] for b in range(n,len(self.rows))],verdepth=self.verdepth)
			if trail == ming[:len(trail)]:
				yoob = reassembled.compacrecurse(yoks,trail,prep,frame,then,earlyabort)
				return yoob
			yoob = (ming,frame,reassembled,earlyabort)
			return yoob

		def namerical(lim,names,sof):
			if type(names) is not list: return [(lim,sof)]
			i = []
			for j in range(len(names)):
				i = i+namerical(lim+len(i),names[j],sof+[j])
			return i
		startindesc = indesc
		thot = prep
		for n in range(len(self.rows)):
			row = self.rows[n]
			rowtype = row.type.verify(indesc.reroll())
			if self.rows[n].obj != None:
				obj = self.rows[n].obj.verify(indesc.reroll(),rowtype) 
			else:
				obj = None
				lentotal = len(indesc)
				lentho   = len(thot)
				lencom1  = lentotal - lentho
				try:
					for k in range(len(yoks)):
						if yoks[k][0] == trail+[n]:
							if yoks[k][2] != False:
								if yoks[k][2] != True:

									st = len(yoks)
									othertype = yoks[k][2].dpush(ScopeDelta([(lentho,lencom1)]))
									obj       = yoks[k][1].dpush(ScopeDelta([(lentho,lencom1)]))

									# trimmy = indesc.trimabsolute(len(thot))
									# assert 'R_comp_pack' not in othertype.prepr()

									# R_comp_pack
									# print("INTO implicitcast: ",obj.prepr(FormatterObject(indesc)))

									obj = implicitcast(indesc,rowtype,othertype,obj,blame=yoks[k][1],soften=earlyabort,extract=yoks,thot=thot,odsc=lencom1,owner=trail+[n])

									# succeeded = rowtype.compare(othertype,lencom1,thot,yoks)
									# for kt in range(st,len(yoks)): yoks[kt] = (yoks[kt][0],yoks[kt][1],yoks[kt][2],trail+[n])
									# if not succeeded:
									# 	if earlyabort:
									# 		while st<len(yoks): del yoks[st]
									# 	raise TypeMismatch(yoks[k][1],rowtype,othertype,indesc).soften(earlyabort)
									ming = getming(thot,st)
									if ming!=None: return restart(thot,ming)
								else:
									obj = yoks[k][1].dpush(ScopeDelta([(lentho,lencom1)]))
								if rowtype.quickdetect(ScopeDelta([(-lentho,lencom1)])): raise CouldNotDeduceType(yoks[k][1]).soften(earlyabort)
								break
							# if force:
							# 	obj = yoks[k][1].verify(indesc,rowtype)
							# 	yoks[k] = (yoks[k][0],obj.dpush(ScopeDelta([(-lentho,lencom1)])),True)
							# 	break

							if rowtype.quickdetect(ScopeDelta([(-lentho,lencom1)])):
								if type(yoks[k][1]) is Lambda and not yoks[k][1].obj.needscarry():
									try:
										truncargs,ntype = rowtype.extractfibration(indesc,yoks[k][1].si,blame=yoks[k][1])
									except InvalidSplit as u:
										raise u.soften(earlyabort)
									try:
										yasat = truncargs.ddpush(-lentho,lencom1) if lentho else truncargs
									except DDpushError: pass
									else:
										trimmy = indesc.trimabsolute(len(thot))
										# coalesce = 
										earlyabort = False

										yasatflat = yasat.flatten(trimmy.reroll(),yoks[k][1].si,needrowtypes=True)

										obj,ntyp = yoks[k][1].obj.verify(trimmy.addflat(yasatflat),reqtype=True)


										obj  =  obj.addlambdasphase2(yoks[k][1].si,pos=yoks[k][1])
										ntyp = ntyp.addfibration(yasat)

										yoks[k] = (yoks[k][0],obj,ntyp)

										st = len(yoks)

										obj  =  obj.dpush(ScopeDelta([(lentho,lencom1)]))
										ntyp = ntyp.dpush(ScopeDelta([(lentho,lencom1)]))


										obj = implicitcast(indesc,rowtype,ntyp,obj,blame=yoks[k][1],soften=earlyabort,extract=yoks,thot=thot,odsc=lencom1,owner=trail+[n])

										# succeeded = ntype.compare(two,lencom1,thot,yoks)
										# for kt in range(st,len(yoks)): yoks[kt] = (yoks[kt][0],yoks[kt][1],yoks[kt][2],trail+[n])
										# if not succeeded:
										# 	raise TypeMismatch(yoks[k][1],ntype,two,indesc.sneakadd(truncargs.flatten(indesc.reroll(),yoks[k][1].si,needrowtypes=True)))

										ming = getming(thot,st)
										if ming!=None: return restart(thot,ming)
										if rowtype.quickdetect(ScopeDelta([(-lentho,lencom1)])): raise CouldNotDeduceType(yoks[k][1]).soften(earlyabort)
										break

								# if not force:break
								break
								raise CouldNotDeduceType(yoks[k][1]).soften(earlyabort)

							earlyabort = False
							obj = yoks[k][1].verify(indesc,rowtype)
							yoks[k] = (yoks[k][0],obj.dpush(ScopeDelta([(-lentho,lencom1)])),True)
							break
				except LanguageError as u:
					raise u.addparameterdata(yoks,trail+[n],len(thot),rowtype,indesc)
			if any(len(o[0])>len(trail)+1 and o[0][:len(trail)+1] == trail+[n] for o in yoks):
				assert obj == None
				moro = rowtype.compacrecurse(yoks,trail+[n],thot,indesc,earlyabort=earlyabort)


				if len(moro)==4:#this is broken...?????
					ming,frame,moro,earlyabort = moro
					obj = SubsObject(len(indesc)) if moro.isemptytype() else None
					cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
					reassembled = DualSubs(cu+[self.rows[j] for j in range(n+1,len(self.rows))],verdepth=self.verdepth)
					if trail == ming[:len(trail)]:
						return reassembled.compacrecurse(yoks,trail,prep,frame,then,earlyabort)
					return (ming,frame,reassembled,earlyabort)
				moro,earlyabort = moro
				obj = SubsObject(len(indesc)) if moro.isemptytype() else None
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				# obj = row.obj.verify(indesc.reroll()) if row.obj != None else obj if obj != None else None
				cu.append(TypeRow(row.name,rowtype,obj,self.rows[n].silent))
			thot = thot+namerical(len(indesc),self.rows[n].name,trail+[n])
			if type(self.rows[n].name) is not list and not indesc.oprows.verified:
				insf = TypeRow(self.rows[n].name,rowtype,obj,self.rows[n].silent)
				indesc = indesc.sneakadd(ScopeObject([insf]))
			else:
				indesc = indesc.sneakadd(self.rows[n].type.flatten(indesc.reroll(),self.rows[n].name,obj=obj,needrowtypes=True))
		for n in range(len(self.rows)):
			for yok in yoks:
				if yok[0] == trail+[n] and cu[n].obj==None:
					raise CouldNotDeduceType(yok[1]).addparameterdata(yoks,trail+[n],len(thot),None,indesc).soften(earlyabort)
					# raise LanguageError(yok[1],"Cannot infer type of parameter.")
		outp = DualSubs(cu,verdepth=self.verdepth,pos=self)
		return ((outp,earlyabort),indesc) if then else (outp,earlyabort)

	def applytemplate(self,indesc,NSC,subs,rows,blame=None):
		poppo = [(NSC[0][a],NSC[1][a]) for a in range(len(NSC[0]))]
		inc = []
		def triplecopy(ma):
			if type(ma) is list: return [triplecopy(k) for k in ma]
			for swap in range(len(poppo)):
				if poppo[swap][0]==ma:
					res = poppo[swap][1]
					inc.append(True)
					del poppo[swap]
					return res
			inc.append(False)
			return ma
		NANms = triplecopy([a.name for a in self.rows])
		for pop in range(len(poppo)): raise LanguageError(blame,"cannot complete renaming statement: "+poppo[pop][0]+" was not found.")

		wlist = self.flatten(indesc.reroll(),NANms,needrowtypes=True).flat
		wonk = indesc.addflat(ScopeObject(wlist)).prepushPR(ScopeDelta([(1,indesc.beginlen()+n) for n in range(len(wlist)) if not inc[n]]))
		

		jmore = DualSubs(rows,verified=False,pos=blame).verify(wonk).flatten(wonk.reroll(),needrowtypes=True).flat

		wclist = [((wlist+jmore)[d],(inc+[True for j in jmore])[d],len(indesc)+d,[],None) for d in range(len(inc)+len(jmore))]
		for a in range(len(wclist)):
			for b in range(a):
				if wclist[b][0].obj==None and wclist[a][0].detect(ScopeDelta([(-1,len(indesc)+b)])) or wclist[b][0].obj!=None and wclist[a][0].deepsoftdetect(ScopeDelta([(-1,len(indesc)+b)])):
					wclist[a][3].append(len(indesc)+b)
					for c in wclist[b][3]:
						if c not in wclist[a][3]: wclist[a][3].append(c)

		dn = copy.copy(subs)
		while len(dn):
			if dn[0].name!=None and dn[0].name[0] in dn: continue
			for a in range(len(wclist)):
				if wclist[a][0].obj==None:
					if dn[0].name==None or dn[0].name[0]==wclist[a][0].name:
						# everything without a ref | everything with a ref.
						wlist = []
						inc   = []
						tub = []
						usedref = []
						for b in range(len(wclist)):
							if b!=a and wclist[a][2] not in wclist[b][3]:
								wlist.append(wclist[b][0].dpush(ScopeDelta(tub)))
								inc.append(wclist[b][1])
								usedref.append(b)
							else:
								tub.insert(0,(-1,len(indesc)+b))
						wonk = indesc.addflat(ScopeObject(wlist)).prepushPR(ScopeDelta([(1,indesc.beginlen()+n) for n in range(len(wlist)) if not inc[n]]))
						ltype = wclist[a][0].type.dpush(ScopeDelta([(len(wlist)-a,len(indesc)+a)]))

						if dn[0].name==None or len(dn[0].name)==1:
							yarn = TypeRow(wclist[a][0].name,ltype,dn[0].obj.verify(wonk,ltype),wclist[a][0].silent)
							del dn[0]
							converter = None
						else:
							if type(wclist[a][0]) is not DualSubs: raise LanguageError(blame,"Tried to subaccess thing that doesn't have subproperties "+str(dn[0].name))
							desc = []
							for o in reversed(range(len(dn))):
								if dn[o].name!=None and dn[o].name[0]==wclist[a][0].name and len(dn[o]).name>1:
									desc.append(dn[o])
									del dn[o]

							yarn = TypeRow(wclist[a][0].name,ltype.applytemplate(wonk,([],[]),desc,[],blame=blame),None,wclist[a][0].silent)
							converter = TypeRow(
								yarn.name,
								ltype,
								implicitcast(
									indesc.reroll().addflat([j for j in wclist[:b+1]]),
									ltype,
									yarn.type,
									RefTree(len(indesc)+b,verdepth=len(indesc)+b+1)
								)
							)
						# everything A refs | A | everything else
						# everything A refs: [first half only has elements dropped, second half only has elements dropped] (like first range subset, but even more are dropped.)
						# A: [introductions and drops, no swaps]
						# everything else: [lots of swaps, no drops, some introduced]

						#everything else needs a depth switch? (yes) (previous elements have been rearranged.)

						so1 = []
						so2 = []
						ql1 = []
						ql2 = []
						hs = len(indesc)
						for b in usedref:
							if wclist[b][2] not in wclist[a][3] and wclist[a][2] not in wclist[b][3]:
								if wclist[b][0].obj==None and yarn.detect(ScopeDelta([(-1,hs)])) or wclist[b][0].obj!=None and yarn.deepsoftdetect(ScopeDelta([(-1,hs)])):
									wclist[a][3].append(wclist[b][2])
									for c in wclist[b][3]:
										if c not in wclist[a][3]: wclist[a][3].append(c)
									for c in range(len(wclist)):
										if wclist[a][2] in wclist[c][3]:
											for d in wclist[a][3]:
												if d not in wclist[c][3]: wclist[c][3].append(d)
							hs+=1
						for b in range(len(wclist)):
							if a==b: continue
							if wclist[b][2] in wclist[a][3]:
								ql1.append(wclist[b])
								so1.append(b)
							else:
								ql2.append(wclist[b])
								so2.append(b)
						sources = so1+[a]+so2
						wclist = ql1+[(yarn,wclist[a][1],wclist[a][2],wclist[a][3])]+ql2
						sourcref = wclist[a][2]
						for b in range(len(sources)):
							if sources[b]==a:
								tub = []
								for c in range(b,len(wclist)):#doesnt reference by old standard is different than by new standard...
									hs = len(indesc)
									for u in usedref:
										if sources[c] == u:
											tub.append((-1,hs))
											break
										hs+=1
								tub = sorted(tub,key=lambda x:-x[1])
								wclist[b] = (yarn.dpush(ScopeDelta(tub)),wclist[b][1],wclist[b][2],wclist[b][3])
							else:
								tub1 = []
								tub2 = []
								tub3 = []
								for c in range(b):
									if sources[b]<sources[c]:
										tub1.append((1,len(indesc)+c))
								for c in sources[b+1:]:
									if sources[b]>c:
										tub2.append((-1,len(indesc)+c))
								hacakewalk = copy.copy(sources)
								for c in range(b):
									for d in range(c):
										if hacakewalk[c]<hacakewalk[d] and hacakewalk[d]<hacakewalk[b]:
											tub3.append((len(indesc)+hacakewalk[c],1,len(indesc)+hacakewalk[d],1))
											swp = hacakewalk[c]
											hacakewalk[c] = hacakewalk[d]
											hacakewalk[d] = swp
								tub = tub3+sorted(tub2,key=lambda x:-x[1])+sorted(tub1,key=lambda x:x[1])

								if sourcref in wclist[b][3]:
									if converter==None:
										wclist[b] = (wclist[b][0].vershortcut(indesc.reroll().addflat(ScopeObject([j[0] for j in wclist[:b]])).prepushPR(ScopeDelta(tub))),wclist[b][1],wclist[b][2],wclist[b][3])
									else:
										yad = [j for j in wclist[:b]]
										yad.insert(b+1,converter)
										wclist[b] = (wclist[b][0].vershortcut(indesc.reroll().addflat(ScopeObject([j[0] for j in wclist[:b]])).prepushPR(ScopeDelta(tub))).postpushPO(ScopeDelta([(-1,len(indesc)+b)])),wclist[b][1],wclist[b][2],wclist[b][3])
								else:
									# print("\n\n\n")
									# print(wclist[b][0].name)
									# print(tub)
									# print(tub1)
									# print(tub2)
									# print(tub3)
									# print([i[0].name for i in wclist])
									wclist[b] = (wclist[b][0].dpush(ScopeDelta(tub)),wclist[b][1],wclist[b][2],wclist[b][3])
						break
			else:
				raise VariableAssignmentError(blame,dn[0][0])

		def unlongcount(si,map,lc=0):
			if type(si) is list:
				res = []
				for i in si:
					k,lc = unlongcount(i,map,lc)
					res.append(k)
				return (res,lc)
			for i in range(len(map)):
				if map[i]==len(indesc)+lc: return (i,lc+1)
			assert False

		return DualSubs([i[0] for i in wclist],verdepth=len(indesc),pos=blame,src=(self,unlongcount(NANms,[i[2] for i in wclist])[0]))

class SubsObject(Tobj):
	@initTobj
	def __init__(self,subs=None,verdepth=None):
		# def _dbgEnter():
		# 	for sub in subs:
		# 		assert type(sub) is SubRow
		self.subs = subs if subs != None else []
		if verdepth!=None:
			self.touches = set()
			self.softtouches = set()
			self.verdepth = verdepth
			self.complexity = 1
			for sub in self.subs:
				assert type(sub) is SubRow#safemode
				self.touches.update(sub.obj.touches)
				self.softtouches.update(sub.obj.softtouches)
				self.complexity += sub.obj.complexity
	def primToJSON(self):
		return {
			"SubsObject",#"type":
			[k.primToJSON() for k in self.subs]#"subs":
		}
	def toJSON(self):
		return {
			"type":"SubsObject",
			"subs":[k.toJSON() for k in self.subs]
		}
	@altPrepr
	def prepr(self,context):
		res = context.red("(")+",".join([k.prepr(context) for k in self.subs])+context.red(")")
		return res
	@altPmultiline
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		pmultilinecsv(context,out,indent,self.subs,prepend+context.red("("),context.red(")")+postpend,callback=callback)

	def isemptyinst(self,si,prep=None):
		if type(si) is not list: return False
		if len(si)!=len(self.subs): return False
		return all(self.subs[k].obj.isemptyinst(si[k],prep=prep) for k in range(len(si)))

	def ddpush(self,amt,lim,repls=None,replsrc=None):
		return SubsObject([k.ddpush(amt,lim,repls,replsrc) for k in self.subs],pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc))
	def detect(self,ranges):
		return any(sub.detect(ranges) for sub in self.subs)
	def dpush(self,pushes):
		return SubsObject([k.dpush(pushes) for k in self.subs],pos=self,verdepth=None if self.verdepth==None else self.verdepth+pushes.lenchange(),altversion=self.dpushalt(pushes))
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is not SubsObject: return False
		if len(self.subs) != len(other.subs): return False
		return all(self.subs[k].compare(other.subs[k],odsc,thot,extract,lefpush,rigpush) for k in range(len(self.subs)))
	def phase1(self,indesc):
		def _dbgEnter():
			indesc.setSafety(0)
			self.setSafety(indesc.beginlen())
		return [(s.name,(s.obj,False)) if s.obj.needscarry() or s.obj.verified else (s.name,s.obj.verify(indesc,reqtype=True)) for s in self.subs]
	def phase1_gentle(self):
		def _dbgEnter():
			self.setVerified()
		for s in self.subs: assert s.name == None
		return [(None,(s.obj,True)) for s in self.subs]
	def phase1_paranoid(self):
		return [(s.name,(s.obj,False)) for s in self.subs]
	def needscarry(self):
		return True
		# return any(k.name!=None or k.obj.needscarry() for k in self.subs)
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		if indesc.oprows.verified:
			return SubsObject([SubRow(None,k.obj.verify(indesc)) for k in self.subs],verdepth=len(indesc),pos=self)

		if carry==None:  raise TypeRequiredError(self,False)
		if type(carry) is not DualSubs:
			ocarry = carry.mangle_UE() if type(carry) is RefTree else None
			if ocarry == None: raise NonUnionTypeError(self,carry,indesc)
			carry = ocarry

		oflow = []
		garbo = carry.compacassign(self.phase1(indesc),overflow=oflow)
		if len(oflow): raise VariableAssignmentError(self,oflow[0][0])

		try:
			st = carry.peelcompactify(indesc,garbo,earlyabort=False)[0]
		except LanguageError as u:
			u.callingcontext([("(Constructing element of union)",carry,len(indesc),indesc,None)],0)
			raise u

		return SubsObject(st.extractbetween(carry),verdepth=len(indesc),pos=self,altversion=self.verifyalt(indesc,carry))


class Template(Tobj):
	@initTobj
	def __init__(self,src,NSC=None,rows=None,subs=None):
		# assert type(subs) is SubsObject
		self.NSC = ([],[]) if NSC==None else NSC
		self.rows = [] if rows == None else rows
		self.subs = [] if subs == None else subs
		self.src = src
	def primToJSON(self):
		return (
			"Template",#"type":
			self.NSC,#"NSC":
			[k.primToJSON() for k in self.rows],#"mix":
			[k.primToJSON() for k in self.subs],#"mix":
			self.src.primToJSON()#"src":
		)
	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assert not then
		assertstatequal(indesc,self,carry,RefTree(verdepth=len(indesc)))
		src = self.src.verify(indesc,RefTree(verdepth=len(indesc)))
		if type(src) is not DualSubs:
			raise LanguageError(self,"Can only apply templating to {"+"} object.")
		if len(self.NSC[0])!=len(self.NSC[1]):
			raise LanguageError(self,"Renaming statements must have an equal number of names on both sides.")
		for k in self.NSC[0]+self.NSC[1]:
			if type(k) is list: raise LanguageError(self,"You can't recursively nest renaming statements.")
		outp = src.applytemplate(indesc,self.NSC,self.subs,self.rows,self)
		if reqtype: return (outp,RefTree(verdepth=len(indesc)))

		# assert outp.src!=None
		return outp







	@altPrepr
	def prepr(self,context):
		add = []
		# if len(self.NSC[0])==0 and len(self.NSC[1])==0: add=[]
		# elif self.NSC[0]==self.NSC[1]: add = [pmultilinelist(self.NSC[0],context)]
		# else: add = [pmultilinelist(self.NSC[0],context)+"="+pmultilinelist(self.NSC[1],context)]
		return self.src.prepr(context)+"<"+",".join(add+[k.prepr(context) for k in self.rows]+[k.prepr(context) for k in self.subs])+">"
	@altPmultiline
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		def calls(context_,out,prepend):
			pmultilinecsv(context,out,indent,self.rows+self.subs,prepend+"<",">"+postpend,callback=callback)
		self.src.pmultiline(context,out,indent,prepend,"",calls)
class Lambda(Tobj):
	@initTobj
	def __init__(self,si,obj,verdepth=None):
		self.si = si
		# assert len(si)>0
		self.obj = obj
		if verdepth!=None:
			self.verdepth = verdepth
			self.complexity = 1+self.obj.complexity
			self.touches = {k for k in self.obj.touches if k<verdepth}
			self.softtouches = {k for k in self.obj.softtouches if k<verdepth}
	def primToJSON(self):
		return (
			"Lambda",#"type":
			self.si,#"si":
			self.obj.PJID#"obj":
		)
	def toJSON(self):
		return {
			"type":"Lambda",
			"si":self.si,
			"obj":self.obj.toJSON()
		}
	def ddpush(self,amt,lim,repls=None,replsrc=None):
		return Lambda(self.si,self.obj.ddpush(amt,lim,repls,replsrc),pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc))
	def detect(self,ranges):
		return self.obj.detect(ranges)
	def dpush(self,pushes):
		return Lambda(self.si,self.obj.dpush(pushes),pos=self,verdepth=None if self.verdepth==None else self.verdepth+pushes.lenchange(),altversion=self.dpushalt(pushes))

	def isemptyinst(self,si,prep=None):
		lc = striphuman(self.verdepth,self.si)[0]
		prep = lc if prep==None else prep+lc
		return self.obj.isemptyinst(si,prep=prep)

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is not Lambda: return False
		return conservativeeq(self.si,other.si) and self.obj.compare(other.obj,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		if len(self.si) == 0: return self.obj.needscarry()
		return True
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		if len(self.si) == 0: return self.obj.verify(indesc,carry,reqtype,then)
		if indesc.oprows.verified:
			return self.obj.verify(indesc.addflat(ScopeObject(flattenunravel(self.si)))).addlambdasphase2(self.si,pos=self).addalts(self.verifyalt(indesc,carry))
		else:
			if carry==None: raise TypeRequiredError(self,True)
			truncargs,ntype = carry.extractfibration(indesc,self.si,blame=self)
			flatver,converter = truncargs.flatten(indesc.reroll(),self.si,then=True,needrowtypes=not indesc.oprows.verified)
			nindesc = indesc.addflat(flatver)
			return self.obj.verify(nindesc,ntype.verify(converter)).addlambdasphase2(self.si,pos=self).addalts(self.verifyalt(indesc,carry))

	def addexob(self,exob):
		jsi = self.si[:len(exob.subs)] if len(self.si)>len(exob.subs) else self.si

		mansc = ScopeObject([TypeRow(None,None)]*self.verdepth,None,None,ContextYam(verified=True)).invisadd(ScopeObject(flattenunravel(jsi,SubsObject(exob.subs[:len(self.si)]) if len(exob.subs)>len(self.si) else exob)))

		if mansc.beginlen()!=self.obj.verdepth:
			print("adding exob: ")

			print("\t",self.si,len(exob.subs))
			print("\t",self.verdepth)
			print("\t",jsi)
			print("\t",flattenunravel(jsi,SubsObject(exob.subs[:len(self.si)]) if len(exob.subs)>len(self.si) else exob))
			print("\t",mansc.beginlen())
			print("\t",self.obj.verdepth)

		jobj = self.obj
		if len(self.si)>len(exob.subs): jobj = jobj.addlambdasphase2(self.si[len(exob.subs):])
		jobj = jobj.verify(mansc)
		if len(exob.subs)>len(self.si): jobj = jobj.addexob(SubsObject(exob.subs[len(self.si):],verdepth=self.verdepth).dpush(ScopeDelta([(jobj.verdepth-self.verdepth,self.verdepth)])))
		return jobj.addalts([k.addexob(exob) for k in self.altversion])


	@altPrepr
	def prepr(self,context):
		word = context.newcolors(self.si)
		return pmultilinelist(self.si,context,word)+self.obj.prepr(context.addbits(word))
	@altPmultiline
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		word = context.newcolors(self.si)
		self.obj.pmultiline(context.addbits(word),out,indent,prepend+pmultilinelist(self.si,context,word),postpend,callback)
class Strategy(Tobj):
	@initTobj
	def __init__(self,args=None,type=None,verdepth=None):
		self.args = DualSubs(pos=pos,verdepth=verdepth) if args == None else args
		self.type = type
		self.verdepth = verdepth
		if verdepth!=None:
			self.touches = set()
			self.softtouches = set()
			self.touches.update(self.args.touches)
			self.softtouches.update(self.args.softtouches)
			self.complexity = 1+self.args.complexity+self.type.complexity
			if self.type!=None:
				self.touches.update(self.type.touches)
				self.softtouches.update(self.type.softtouches)
			self.touches = {k for k in self.touches if k<verdepth}
			self.softtouches = {k for k in self.softtouches if k<verdepth}
	def primToJSON(self):
		return (
			"Strategy",#"type":
			None if self.type==None else self.type.PJID,#"cent":
			[k.PJID for k in self.args.rows]#"rows":
		)
	def toJSON(self):
		return {
			"type":"Strategy",
			"cent":self.type.toJSON(),
			"rows":self.args.toJSON()["rows"]
		}
	def ddpush(self,amt,lim,repls=None,replsrc=None):
		disgrace = ScopeDelta()
		newargs = self.args.ddpush(amt,lim,repls,replsrc,disgrace=disgrace)
		
		newtype = self.type
		if not disgrace.isempty(): newtype = newtype.dpush(disgrace)
		newtype = newtype.ddpush(amt,lim,repls,replsrc)
		return Strategy(newargs,newtype,pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc))
	def detect(self,ranges):
		ranges = ranges.isolate()
		return self.args.detect(ranges,merge=True) or self.type.detect(ranges)
	def dpush(self,pushes):
		disgrace = ScopeDelta()
		newargs = self.args.dpush(pushes,disgrace=disgrace)
		newtype = self.type.dpush(disgrace+pushes)
		return Strategy(newargs,newtype,pos=self,verdepth=None if self.verdepth==None else self.verdepth+pushes.lenchange(),altversion=self.dpushalt(pushes))


	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is RefTree:
			att = other.mangle_FE()
			if att!=None: return self.compare(att,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not Strategy: return False
		if len(other.args)<len(self.args) and type(other.type) is RefTree:
			att = other.type.mangle_FE()
			if att!=None: return self.compare(Strategy(other.args+att.args,att.type),odsc,thot,extract,lefpush,rigpush)
		if lefpush==None: lefpush = ScopeDelta()
		if rigpush==None: rigpush = ScopeDelta()
		lefpush = lefpush.isolate()
		rigpush = rigpush.isolate()
		adv = []
		st = len(lefpush.pushes)
		if not self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush,keepr=True,advanced=adv): return False
		# print(adv)
		if len(adv):
			mdsc = self.verdepth+lefpush.lenchange()+longcount(self.args)-rigpush.lenchange()#longcount([k.name for k in adv])
			other = Strategy(DualSubs(adv,verdepth=mdsc),other.type,verdepth=mdsc)
		else:
			other = other.type
		return self.type.compare(other,odsc,thot,extract,lefpush,rigpush)
	def addfibration(self,args):
		return Strategy(args+self.args,self.type,pos=self,verdepth=self.verdepth-longcount(args),altversion=self.fibrationalt(args))
	def fulavail(self):
		return self.type.fulavail()
	def semavail(self,mog):
		return self.type.semavail(mog)
	def emptyinst(self,limit,mog,prep=None):

		# emptyinst now requires knowledge of its depth...

		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)
		sc = longcount(self.args.semavail())
		if prep == None: prep = (SubsObject(verdepth=limit),limit)
		prep = prep[0].dpush(ScopeDelta([(limit+sc-prep[1],prep[1])])).subs if prep != None else []

		return Lambda(self.args.semavail(),self.type.emptyinst(limit+sc,mog,(SubsObject(prep+self.args.emptyinst(limit).subs,verdepth=limit+sc),limit+sc)),verdepth=limit)
	def trimallnonessential(self,si=None):

		disgrace = ScopeDelta()
		nargs = self.args.trimallnonessential(si,disgrace)
		ntype = self.type
		if not disgrace.isempty(): ntype = ntype.dpush(disgrace)
		return Strategy(nargs,ntype,verdepth=self.verdepth,pos=self,altversion=self.altversion)
	@lazyflatten
	def flatten(self,indesc,mog,assistmog,prep=None,obj=None,fillout=None,then=False):
		if obj != None:
			obj = obj.addexob(self.args.emptyinst(len(indesc)))

		arflat = self.args.flatten(indesc,needrowtypes=False)

		arp = self.args.verify(indesc)

		if prep == None:
			njprep = (arp,len(indesc))
		else:
			calmdown = prep[0].dpush(ScopeDelta([(len(indesc)-longcount(prep[0])-prep[1],prep[1])]))
			njprep = (DualSubs(calmdown.rows+arp.rows,verdepth=calmdown.verdepth),len(indesc)-longcount(prep[0]))

		return self.type.flatten(indesc.addflat(arflat),mog,assistmog,njprep,obj,fillout=fillout,then=then,needrowtypes=True)
	def needscarry(self):
		if len(self.args) == 0: return self.type.needscarry()
		return False
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		verargs,thendesc = self.args.verify(indesc,then=True)
		if len(verargs) == 0:
			thendesc = thendesc.posterase(len(indesc))
			return self.type.verify(thendesc,carry,reqtype=reqtype,then=then)#.addalts(self.verifyalt(indesc,carry))

		if not self.verified: assertstatequal(indesc,self,carry,RefTree(verdepth=len(indesc)))
		vertype = self.type.verify(thendesc,RefTree(verdepth=len(thendesc)),then=then)
		if then: vertype,th = vertype
		salts = self.verifyalt(indesc,carry)
		if type(vertype) is Strategy:
			salts = salts + vertype.fibrationalt(verargs)
			verargs = verargs + vertype.args
			vertype = vertype.type
		outp = Strategy(args=verargs,type=vertype,pos=self,verdepth=len(indesc),altversion=salts)
		return (outp,RefTree(verdepth=len(indesc))) if reqtype else (outp,th) if then else outp
	@altPrepr
	def prepr(self,context):
		if context.littleeasier and any(row.obj!=None for row in self.args.rows) and self.verdepth!=None:
			return self.trimallnonessential().prepr(context)
		res = []
		for k in self.args.rows:
			word = context.newcolors(k.name)
			res.append(k.prepr(context,word=word))
			context = context.addbits(word)
		return context.red("[")+",".join(res)+context.red("]")+(self.type.prepr(context) if self.type!=None else "None")
	@altPmultiline
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		if context.littleeasier and any(row.obj!=None for row in self.args.rows) and self.verdepth!=None:
			return self.trimallnonessential().pmultiline(context,out,indent,prepend,postpend,callback)
		def calls(context,out,prepend):
			self.type.pmultiline(context,out,indent,prepend,postpend,callback=callback)
		pmultilinecsv(context,out,indent,self.args.rows,prepend+context.red("["),context.red("]"),lamadapt=lambda x:x.name,callback=calls,delim=context.red(","))
class RefTree(Tobj):
	@initTobj
	def __init__(self,name=None,args=None,src=None,safety=None,verdepth=None,cold=False):
		self.name   = 0 if name == None else name
		self.args   = SubsObject(verdepth=verdepth) if args == None else args
		self.src    = src
		self.cold = cold
		self.safety = safety
		if verdepth!=None:
			self.touches = set()
			self.softtouches = set()
			self.verdepth = verdepth
			self.complexity = 1+(self.src.complexity if self.src!=None else 0) + self.args.complexity
			self.touches.update(self.args.touches)
			self.softtouches.update(self.args.softtouches)
			if self.src!=None: self.touches.update(self.src.touches)
			if self.src!=None: self.softtouches.update(self.src.softtouches)
			if type(self.name) is int and self.src==None:
				assert self.name<verdepth or self.name==0
				if not self.cold: self.touches.add(self.name)
				else: self.softtouches.add(self.name)

			assert self.src==None or type(self.src) is RefTree or type(self.src.core) is RefTree
		assert type(self.args) is SubsObject
	def primToJSON(self):
		return {
			"RefTree",#"type":
			self.name,#"name":
			[k.primToJSON() for k in self.args.subs],#"subs":
			None if self.src==None else self.src.PJID#"src":
		}
	def toJSON(self):
		return {
			"type":"RefTree",
			"name":self.name,
			"subs":self.args.toJSON()["subs"],
			"src":None if self.src==None else self.src.toJSON()
		}
	def ddpush(self,amt,lim,repls=None,replsrc=None):
		gy = self.name
		if gy >= lim and self.src == None:
			gy += amt
			if gy-(0 if repls==None else len(repls)) < lim:
				if repls == None: raise DDpushError

				fom = self.ddpush(replsrc-self.verdepth,replsrc) if replsrc-self.verdepth else self#dsc->odsc    lim-amt-len(repls)?
				for j in range(len(repls)):
					if fom.compare(repls[j]): return RefTree(lim+j,verdepth=self.verdepth+amt)
				raise DDpushError
		return RefTree(gy,self.args.ddpush(amt,lim,repls,replsrc),None if self.src == None else self.src.ddpush(amt,lim,repls,replsrc),pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc),cold=self.cold)
	def detect(self,ranges):
		if self.src==None:
			if not ranges.canTranslate(self.name): return True
		elif self.src.detect(ranges): return True
		return self.args.detect(ranges)
	def dpush(self,pushes):
		gy = self.name
		if self.src==None and self.name!=0: gy = pushes.translate(self.name)
		outp = RefTree(gy,self.args.dpush(pushes),None if self.src == None else self.src.dpush(pushes),pos=self,verdepth=None if self.verdepth==None else self.verdepth+pushes.lenchange(),altversion=self.dpushalt(pushes),cold=self.cold)
		if hasattr(self,'debugname'): outp.debugname = self.debugname
		return outp
	def setSafety(self,safe):
		if safe == None: return
		if hasattr(self,'foclnsafety'): assert self.foclnsafety == safe
		else:
			self.foclnsafety = safe
			downdeepverify(self,safe)

		if safe!=None:
			if self.src==None and type(self.name) is int and self.name!=0: assert self.name<safe

	def isemptyinst(self,si,prep=None):
		if type(si) is list: return False
		if self.name!=si: return False
		return self.args.isemptyinst([] if prep==None else prep)

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if self.src != None:
			if type(other) is not RefTree: return False
			if other.src == None or not self.src.compare(other.src,odsc,thot,extract,lefpush,rigpush): return False
		elif thot != None:
			for k in thot:
				if k[0] == self.name:
					for j in extract:
						if j[0] == k[1] and j[2] == False:
							return True
					repls = []
					valid = True
					dsc = self.verdepth+(0 if lefpush==None else lefpush.lenchange())

					for g1 in range(len(self.args.subs)):
						if type(self.args.subs[g1].obj) is not RefTree or self.args.subs[g1].obj.name<odsc:
							valid = False
							break
						for g2 in range(g1):
							if self.args.subs[g1].obj.compare(self.args.subs[g2].obj):
								valid = False
								break
						if not valid: break
						repls.append(self.args.subs[g1].obj)
					if not valid: break
					try:
						gr = other if rigpush==None else other.dpush(rigpush)
						gr = gr.ddpush(odsc+len(repls)-dsc,odsc,repls=repls,replsrc=dsc)
					except DDpushError:
						return False

					mod = gr.addlambdasphase2(["_"]*len(repls))

					# mod = gr if len(repls) == 0 else Lambda(["_"]*len(repls),gr,verdepth=odsc)
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(mod)
					mod.setSafety(odsc)
					extract.append((k[1],mod,True))
					return True
		if type(other) is DualSubs:
			att = self.mangle_UE()
			if att!=None: return att.compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is Strategy:
			att = self.mangle_FE()
			if att!=None: return att.compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not RefTree: return False
		lefname = self.name
		rigname = other.name
		if lefpush != None: lefname = lefpush.translate(lefname)
		if rigpush != None: rigname = rigpush.translate(rigname)
		return lefname == rigname and self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		return False
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assert not then
		if type(self.name) is str and self.name.endswith(".ax'"):
			print([k for k in indesc.oprows.dependencies.keys()])
			assert self.name.replace("'","") in indesc.oprows.dependencies
			assertstatequal(indesc,self,carry,RefTree(verdepth=len(indesc)))
			tue = indesc.oprows.dependencies[self.name.replace("'","")].dpush(ScopeDelta([(len(indesc),0)]))

			return (tue,RefTree(verdepth=len(indesc))) if reqtype else tue

		if indesc.oprows.verified:
			subsres = self.args.verify(indesc)
			if self.src!=None:
				a = self.src.verify(indesc).reference(self.name)
				if len(subsres.subs)==0: return a
				return a.addexob(subsres)
			row = indesc.prepushes.translate(self.name)
			if indesc.flat[row].obj!=None and not self.cold:
				cr  = indesc.postpushes.translateGentle(row)
				ejob = indesc.flat[row].obj.dpush(ScopeDelta([(len(indesc)-cr,min(cr,len(indesc)))]))
				if len(subsres.subs): ejob = ejob.addexob(subsres)
				return ejob.addalts(self.verifyalt(indesc,carry))
			else:
				cr  = indesc.postpushes.translate(row)
				return RefTree(cr,subsres,pos=self,verdepth=len(indesc),cold=self.cold,altversion=self.verifyalt(indesc,carry))

		assert not self.verified
		assert not self.cold
		p1 = self.args.phase1(indesc)

		if type(self.name) is int: assert False


		errorcontext = []
		if self.src == None:
			tra = indesc.symextract(self.name,p1,carry=carry,reqtype=reqtype,safety=self.safety,pos=self,errorcontext=errorcontext)

			if tra != None: return (tra[0].addalts(self.verifyalt(indesc,carry)),tra[1]) if reqtype else tra.addalts(self.verifyalt(indesc,carry))
			if self.verified:
				raise LanguageError(self,"Unknown error...")
			for a in range(len(indesc.flat)):
				if indesc.flat[a].name==self.name and (-indesc.prepushes).canTranslate(a):
					raise LanguageError(self,"Symbol not defined for these arguments: "+self.name).callingcontext(errorcontext,-1)
			raise LanguageError(self,"Symbol not defined in this context: "+self.name).callingcontext(errorcontext,-1)
		else:
			if self.src.needscarry(): raise LanguageError(self,"Need to be able to generate type for property access...")
			orig = self.src.verify(indesc,reqtype=True)
			examtype = orig[1] if type(orig[1]) is DualSubs else orig[1].mangle_UE() if type(orig[1]) is RefTree else None
			if examtype!=None:

				anguish = examtype.flatten(indesc.reroll(),obj=orig[0],needrowtypes=True)
				tra = indesc.invisadd(anguish).preerase(len(anguish)).symextract(self.name,p1,carry=carry,reqtype=reqtype,safety=self.safety,limiter=len(indesc.flat),pos=self,errorcontext=errorcontext)
				if tra != None: return (tra[0].addalts(self.verifyalt(indesc,carry)),tra[1]) if reqtype else tra.addalts(self.verifyalt(indesc,carry))
			# if self.name=="construct":
			# 	print(orig[0])
			# 	print(orig[0].altversion)
			for possib in [orig[0]]+orig[0].altversion:
				if type(possib) is RefTree and possib.src == None:

					retrievalname = indesc.flat[(-indesc.postpushes).translate(possib.name)].name
					print("RETRIEVALNAME: ",retrievalname)

					tra = indesc.symextract(retrievalname+"."+self.name,possib.args.phase1_gentle()+p1,reqtype=reqtype,carry=carry,safety=self.safety+len(possib.args.subs) if self.safety!=None else None,pos=self,cosafety=len(possib.args.subs),errorcontext=errorcontext)
					if tra != None: return (tra[0].addalts(self.verifyalt(indesc,carry)),tra[1]) if reqtype else tra.addalts(self.verifyalt(indesc,carry))
			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,carry=carry,safety=self.safety+1 if self.safety!=None else None,pos=self,errorcontext=errorcontext)
			if tra != None: return (tra[0].addalts(self.verifyalt(indesc,carry)),tra[1]) if reqtype else tra.addalts(self.verifyalt(indesc,carry))
			raise LanguageError(self,"Symbol not defined for these arguments as a property access, macro, or operator overload: "+self.name).callingcontext(errorcontext,-1)
	@altPrepr
	def prepr(self,context):
		res = str(context.getname(self.name)) if self.src==None else str(self.name)
		if self.src != None: res = self.src.prepr(context)+"."+res
		if len(self.args.subs)>0: res = res+"("+",".join([k.prepr(context) for k in self.args.subs])+")"
		return res
	@altPmultiline
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		def calls(context_,out,prepend):
			res = str(context.getname(self.name)) if self.src==None else str(self.name)
			if len(self.args.subs)==0:
				if callback == None:
					out.append("\t"*indent+prepend+res+postpend)
				else:
					callback(context,out,prepend+res+postpend)
			else:
				pmultilinecsv(context,out,indent,self.args.subs,prepend+res+"(",")"+postpend,callback=callback)
		if self.src == None: calls(context,out,prepend)
		else: self.src.pmultiline(context,out,indent,prepend,".",callback=calls)

	def mangle_FE(self):
		# indesc = ScopeObject([TypeRow(None,None)]*self.verdepth,None,None,ContextYam(verified=True))
		if self.name==1 and self.src==None and type(self.args.subs[0].obj) is Strategy:
			reduc = self.args.subs[0].obj.trimallnonessential()
			print("self verdepth: ",self.verdepth)
			print("Mangling: ",self.args.subs[1].obj.getSafety())
			print("And: ",reduc.args.emptyinst(self.verdepth).getSafety())
			#<><> reduce redundant calls here...
			despar = ScopeDelta([(reduc.type.verdepth-self.verdepth,self.verdepth)])
			newparams = reduc.args.emptyinst(self.verdepth)
			return Strategy(reduc.args,RefTree(1,SubsObject([
				SubRow(None,reduc.type),
				SubRow(None,self.args.subs[1].obj.dpush(despar).addexob(newparams)),
				SubRow(None,self.args.subs[2].obj.dpush(despar).addexob(newparams))
			],verdepth=reduc.type.verdepth),verdepth=reduc.type.verdepth),verdepth=self.verdepth)
		return None
	def mangle_UE(self):
		indesc = ScopeObject([TypeRow(None,None)]*self.verdepth,None,None,ContextYam(verified=True))
		if self.name==1 and self.src==None and type(self.args.subs[0].obj) is DualSubs:
			trimmed = self.args.subs[0].obj.trimallnonessential()
			substuff = [(self.args.subs[1].obj.reference(s),self.args.subs[2].obj.reference(s)) for s in range(len(trimmed.rows))]

			inhuman = striphuman(self.verdepth,[a.name for a in trimmed])[0]

			outs = []
			alc = self.verdepth
			sofrefs = []
			for a in range(len(trimmed.rows)):
				toalc = ScopeDelta([(alc-self.verdepth,self.verdepth)])
				refs = [a]
				lc = self.verdepth
				for b in range(a):
					tlc = longcount(trimmed.rows[b].name)
					if trimmed.rows[a].type.quickdetect(ScopeDelta([(-tlc,lc)])): refs = sorted(refs+[k for k in sofrefs[b] if k not in refs])
					lc+=tlc
				sofrefs.append(refs)
				nurows = []
				hedge = []
				lc = self.verdepth
				for b in range(a+1):
					tlc = longcount(trimmed.rows[b].name)
					if b in refs:
						nurows.append(trimmed.rows[b].type.dpush(ScopeDelta(hedge)+toalc))
						lc+=tlc
					else: hedge.append([(-tlc,lc)])
				thad = [trimmed.rows[b].name for b in refs[:-1]]
				if len(refs) == 1:
					outs.append(TypeRow(
						trimmed.rows[a].name,
						RefTree(1,SubsObject([
							SubRow(None,trimmed.rows[a].type.verify(indesc).dpush(toalc)),
							SubRow(None,substuff[refs[0]][0].dpush(toalc)),
							SubRow(None,substuff[refs[0]][1].dpush(toalc))
						],verdepth=alc),verdepth=alc)
					))
				elif len(refs) == 2:
					outs.append(TypeRow(
						trimmed.rows[a].name,
						RefTree(1,SubsObject([
							SubRow(None,trimmed.rows[a].type.verify(indesc).dpush(toalc)),
							SubRow(None,
								RefTree(3,SubsObject([
									SubRow(None,nurows[0]),
									SubRow(None,substuff[refs[0]][0].dpush(toalc)),
									SubRow(None,substuff[refs[0]][1].dpush(toalc)),
									SubRow(None,Lambda([thad[0],"_"],nurows[-1].dpush(ScopeDelta([(1,nurows[-1].verdepth)])),verdepth=alc)),
									SubRow(None,outs[refs[0]].type.emptyinst(alc,inhuman[refs[0]])),
									SubRow(None,substuff[a][0].dpush(toalc)),
								],verdepth=alc),verdepth=alc)
							),
							SubRow(None,substuff[a][1].dpush(toalc))
						],verdepth=alc),verdepth=alc)
					))
				else:
					outs.append(TypeRow(
						trimmed.rows[a].name,
						RefTree(1,SubsObject([
							SubRow(None,trimmed.rows[a].type.verify(indesc).dpush(toalc)),
							SubRow(None,
								RefTree(3,SubsObject([
									SubRow(None,DualSubs([TypeRow(trimmed.rows[refs[i]].name,nurows[i]) for i in range(len(refs)-1)],verdepth=alc)),
									SubRow(None,SubsObject([
										SubRow(None,substuff[refs[i]][0].dpush(toalc))
										for i in range(a)
									],verdepth=alc)),
									SubRow(None,SubsObject([
										SubRow(None,substuff[refs[i]][1].dpush(toalc))
										for i in range(a)
									],verdepth=alc)),
									SubRow(None,Lambda([thad,"_"],nurows[-1].dpush(ScopeDelta([(1,nurows[-1].verdepth)])),verdepth=alc)),
									SubRow(None,SubsObject([
										SubRow(None,outs[refs[i]].type.emptyinst(alc,inhuman[refs[i]]))
										for i in range(a)
									],verdepth=alc)),
									SubRow(None,substuff[a][0].dpush(toalc)),
								],verdepth=alc),verdepth=alc)
							),
							SubRow(None,substuff[a][1].dpush(toalc))
						],verdepth=alc),verdepth=alc)
					))
				aalc = longcount(trimmed.rows[a].name)
				alc += aalc
				indesc = indesc.invisadd(trimmed.rows[a].type.flatten(indesc,trimmed.rows[a].name,obj=substuff[a][1],needrowtypes=False))
			return DualSubs(outs,verdepth=self.verdepth)
		return None
	def addexob(self,exob):
		outp = RefTree(self.name,SubsObject(self.args.subs+exob.subs,verdepth=self.verdepth),self.src,pos=self,verdepth=self.verdepth,altversion=[k.addexob(exob) for k in self.altversion],cold=self.cold)
		if hasattr(self,'debugname'): outp.debugname = self.debugname
		return outp

class OperatorSet(Tobj):
	def primToJSON(self):
		return (
			"OperatorSet",#"type":
			[k.PJID if type(k) is not str else k for k in self.array]#"array":
		)
	@initTobj
	def __init__(self,array):
		self.array = array
	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		fulltree = []
		insert = fulltree
		for ind in self.array:
			if type(ind) is str:
				precnest  = indesc.precidence(ind)
				if precnest == None:
					raise LanguageError(self,"Operator not included in sneeze: "+ind)
				if insert == None:
					(prec,nesting) = precnest
					shift = fulltree
					while len(shift[-1]) == 3 and shift[-1][1] < prec or shift[-1][1] == prec and nesting:
						shift = shift[-1][2]
					shift[-1] = (ind,prec,[shift[-1]])
					insert = shift[-1][2]
				else:
					urnary = (ind,precnest[0],[])
					insert.append(urnary)
					insert = urnary[2]
			else:
				insert.append(ind.verify(indesc,reqtype=True))
				insert = None
		def douparse(tree,carry=None):
			if len(tree) == 2: return tree
			p1 = [(None,douparse(u)) for u in tree[2]]
			ghi = indesc.symextract(tree[0],p1,reqtype=True,carry=carry,safety=len(tree[2]),pos=self)
			if ghi == None:
				if tree[0] not in [a.name for a in indesc.flat]:
					raise LanguageError(self,"operator not defined.")
				raise LanguageError(self,"operator not defined for these arguments.")
			return ghi
		outp = douparse(fulltree[0],carry=None)
		return outp if reqtype else outp[0]
	@altPrepr
	def prepr(self,context):
		ssa = []
		for k in self.array:
			if type(k) is str: ssa.append(k)
			elif type(k) is OperatorSet: ssa.append(context.red("(")+k.prepr(context)+context.red(")"))
			else: ssa.append(k.prepr(context))
		return " ".join(ssa)
	@altPmultiline
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		short = self.prepr(context)
		if nonhtmllength(short+prepend)<=context.magic:
			out.append("\t"*indent+prepend+short+postpend)
			return
		rowprep = prepend
		for token in range(len(self.array)):
			if type(self.array[token]) is str:
				rowprep+=self.array[token]+" "
			else:
				if token == len(self.array)-1:
					self.array[token].pmultiline(context,out,indent,rowprep,postpend,callback=callback)
				else:
					self.array[token].pmultiline(context,out,indent,rowprep,"",callback=None)





@v_args(meta=True)
class MyTransformer(Transformer):
	def start(self,children,meta):
		return (children[:-1],children[-1])
	def precrow(self,children,meta):
		if type(children[-1]) is dict:
			return (children[:-1],children[-1])
		return (children,{'associate':'left'})
	def leftassoc(self,children,meta):
		return {'associate':'left'}
	def rightassoc(self,children,meta):
		return {'associate':'right'}
#--------------------------------------------------
	def __init__(self):
		self.dependencies=set()
	def argument(self,children,meta):
		if type(children[0]) is str: return SubRow([k.replace("*****",".") for k in children[0].replace("'.'","*****").split(".")],children[1])
		return SubRow(None,children[0])
	def datapack(self,children,meta):
		if type(children[0]) is str or type(children[0]) is list: return (children[0],children[1])
		return ("*****",children[0])
	def declaration(self,children,meta):
		if type(children[0]) is tuple:
			obj = None
			if len(children)>2:
				obj = children[2]
				# if type(children[1]) is Strategy:
				# 	obj = Lambda(children[1].args.semavail(),obj,verified=False,pos=meta)
			return TypeRow(children[0][0],children[1],obj,children[0][1])
		obj = None
		if len(children)>1:
			obj = children[1]
			# if type(children[0]) is Strategy:
			# 	obj = Lambda(children[0].args.semavail(),obj,verified=False,pos=meta)
		return TypeRow(None,children[0],obj,{'silent':False,'contractible':False})
	def inferreddeclaration(self,children,meta):
		ty = None if len(children)<3 else Strategy(args=children[1],type=None,verified=False,pos=meta)
		return TypeRow(children[0][0],ty,children[-1],children[0][1])
	def interrobangmarker(self,children,meta):
		return {'silent':True,'contractible':True}
	def silentmarker(self,children,meta):
		return {'silent':True,'contractible':False}
	def contractmarker(self,children,meta):
		return {'silent':False,'contractible':True}
	def infermarker(self,children,meta):
		return {'silent':False,'contractible':False}
	def multilabel(self,children,meta):
		return children[0]
	def introducer(self,children,meta):
		return children
	def reftree(self,children,meta):
		if type(children[0]) is str:
			src = None
			name = children[0]
			lim = 1
		else:
			src = children[0]
			name = children[1]
			lim = 2
		safety = None
		args = []
		for j in children[lim:]:
			if safety==None: safety = len(j.subs)
			args += j.subs
		return RefTree(name,SubsObject(args,pos=meta,verified=False),src,safety,pos=meta,verified=False)
	def lamb(self,children,meta):
		coal = []
		for c in children[:-1]:
			coal+=c
		return Lambda(coal,children[-1],pos=meta,verified=False)
	def template(self,children,meta):
		if   len(children)==1: return Template(children[0],pos=meta,verified=False)
		elif len(children)==2: return Template(children[0],None,children[1][0],children[1][1],pos=meta,verified=False)
		elif len(children)==3: return Template(children[0],(children[1],children[1]),children[2][0],children[2][1],pos=meta,verified=False)
		elif len(children)==4: return Template(children[0],(children[1],children[2]),children[3][0],children[3][1],pos=meta,verified=False)
		else: assert False
	def mixedsubs(self,children,meta):
		return ([c for c in children if type(c) is TypeRow],[c for c in children if type(c) is SubRow])

	def strategy(self,children,meta):
		args = []
		for j in children[:-1]:
			args += j.rows
		return Strategy(DualSubs(args,verified=False,pos=meta),children[-1],pos=meta,verified=False)
	def string(self,children,meta):
		if str(children[0]).endswith(".ax'"):
			self.dependencies.add(str(children[0]).replace("'",""))
			return str(children[0])
		return str(children[0]).replace("'","")
	def operators(self,children,meta):
		return OperatorSet(children,pos=meta,verified=False)
	def subsobject(self,children,meta):

		return SubsObject(children,pos=meta,verified=False)
	def wsubsobject(self,children,meta):
		if len(children):
			if len(children[0].subs) == 1 and children[0].subs[0].name==None:
				return children[0].subs[0].obj
			else:
				return children[0]
		else:
			return SubsObject(pos=meta,verified=False)

	def dualsubs(self,children,meta):
		return DualSubs(children,pos=meta,verified=False)
	def wdualsubs(self,children,meta):
		return children[0] if len(children) else DualSubs(pos=meta,verified=False)

class JSONTransformer:
	def generic(self,json,depth):
		if   json["type"] == "RefTree":    return self.RefTree(json,depth)
		elif json["type"] == "DualSubs":   return self.DualSubs(json,depth)
		elif json["type"] == "Strategy":   return self.Strategy(json,depth)
		elif json["type"] == "SubsObject": return self.SubsObject(json,depth)
		elif json["type"] == "Lambda":     return self.Lambda(json,depth)
		else: assert False
	def RefTree(self,json,depth):
		return RefTree(name=json["name"],args=self.SubsObject(json,depth),src=None if json["src"]==None else self.generic(json["src"],depth),verdepth=depth)
	def DualSubs(self,json,depth):
		rows = []
		cumulative = 0
		for row in json["rows"]:
			rows.append(TypeRow(row["name"],self.generic(row["cent"],depth+cumulative),None if row["obj"]==None else self.generic(row["obj"],depth+cumulative),row["silent"]))
			cumulative+=longcount(row["name"])
		return DualSubs(rows,verdepth=depth)
	def Strategy(self,json,depth):
		args = self.DualSubs(json,depth)
		return Strategy(args,self.generic(json["cent"],depth+longcount(args)),verdepth=depth)
	def SubsObject(self,json,depth):
		return SubsObject([SubRow(None,self.generic(k,depth)) for k in json["subs"]],verdepth=depth)
	def Lambda(self,json,depth):
		return Lambda(json["si"],self.generic(json["obj"],depth+longcount(json["si"])),verdepth=depth)



def compilefiles(files,overrides=None,l=None,basepath="",redoAll=False):
	if l==None:
		with open("core.lark", "r") as f:
			l = Lark(f.read(),parser='lalr', propagate_positions=True)
	if overrides == None: overrides = {}
	for filename in overrides.keys():
		if os.path.exists(filename+".ver"):
			os.remove(filename+".ver")
	if redoAll:
		for filename in files:
			if os.path.exists(filename+".ver"):
				os.remove(filename+".ver")

	verifiles = {}
	impstack = [files]
	active = []
	isnew = {}
	md5s = {}
	while len(impstack):
		if len(impstack[-1])==0:
			impstack.pop()
			if len(active):
				yis = active.pop()
				if yis[0]:
					for exmd5,a in yis[4]:
						if not isnew[a] or md5s[a]!=exmd5:
							transformer = MyTransformer()
							ahjs = transformer.transform(l.parse(yis[2]))
							ver = ahjs[1].verify(ScopeObject([],oprows=ContextYam(ahjs[0],verifiles)),RefTree(verdepth=0))
							isnew[ahjs[1]] = True
							break
					else:
						ver = yis[5]
						isnew[yis[1]] = False
				else:
					ver = yis[2][1].verify(ScopeObject([],oprows=ContextYam(yis[2][0],verifiles)),RefTree(verdepth=0))
					isnew[yis[1]] = True
					print("\n\nverified",yis[1],":",ver)
				with open(basepath+yis[1]+".ver","w") as f:
					json.dump((yis[3],[(md5s[a[1]],a[1]) for a in yis[4]],ver.toJSON()),f, default=lambda o: o.__dict__+{str(o.__type__)})
				md5s[yis[1]] = yis[3]
				verifiles[yis[1]] = ver
			continue
		filename = impstack[-1].pop()
		if filename in [a[1] for a in active]: raise LanguageError(None,"Cyclic import: "+filename)
		if filename in verifiles: continue
		if filename in overrides.keys():
			document = overrides[filename]
		else:
			try:
				with open(basepath+filename,"r",encoding='utf-8') as f: document = f.read()
			except:
				raise LanguageError(None,"Could not import file: "+filename)
		md5 = hashlib.md5(document.encode()).hexdigest()
		try:
			with open(basepath+filename+".ver","r") as f:
				ver = json.load(f)
				assert ver[0]==md5
				found = True
				jsontransformer = JSONTransformer()
				active.append((True,filename,document,md5,ver[1],jsontransformer.generic(ver[2],0)))
				impstack.append({a for a in ver[1]})
		except Exception as u:
			if os.path.exists(basepath+filename+".ver"):
				os.remove(basepath+filename+".ver")
			transformer = MyTransformer()
			active.append((False,filename,transformer.transform(l.parse(document)),md5,[(None,a) for a in transformer.dependencies]))
			impstack.append(transformer.dependencies)




def _dbgTest():
	# compilefiles({"grouptheory.ax","builtin.ax"},redoAll=True)
	# try:
	try:
	# 	# compilefiles({"grouptheory.ax","builtin.ax"},redoAll=True)
		compilefiles({"grouptheory.ax"})
	except LanguageError as u:
		u.tohtml()
		raise u
	# except LanguageError as u:
	# 	u.tohtml()
	# compilefiles({"builtin.ax"},redoAll=True)
	# print("debug")





#<><><><><><> altversion, dualsubs src must be saved to file. (!!!!!!!!!!)

#template can split things apart- need to allow this...<><><><><><>

#on src access, shouldn't it keep track of the maximum number of open accesses, so that when you wrap it in a tuple it can simplify the structure>><<><>





#if the sneeze changes you have to recompile everything.




#len(indesc) could be stored






#list of mangles:
#last: compact variables (tracked through attached object.)




#if the time spent inside the compare function accounts for a significant portion of the runtime, then you should implement a list of previous substitutions to compare instead
#	those ladders may be subbed out already. they vanish when dpush clobbers them.


#you need to fine-tune the operator precidence and associativity.












