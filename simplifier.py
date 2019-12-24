
import copy
from inspect import getfullargspec
from .lark import Transformer, v_args, Tree, Lark
import io

# from .lark
# import lark
# print(lark.__dir__())


import hashlib
# import os.path
import os
import json
from traceback import format_stack
import re
import random
# from pycallgraph import PyCallGraph
# from pycallgraph.output import GraphvizOutput



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



	def downdeepverify(ahjs,amt):
		if type(ahjs) is RefTree:
			if ahjs.src!=None: ahjs.src.setSafety(amt)
			ahjs.args.setSafety(amt)
		if type(ahjs) is SubsObject:
			for j in ahjs.subs: j.setSafetyrow(amt)
		if type(ahjs) is DualSubs:
			compen = 0
			if ahjs.origin!=None: ahjs.origin[0].setSafety(amt)
			for j in ahjs.rows:
				if type(j.type) is Strategy and ahjs.verdepth==None:
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
			if ahjs.src!=None:
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
			if ahjs.verdepth==None: return
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

def _dbgEnter_dpush(self,pushes,exob):
	self.setVerified()
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
	else:
		safe = self.getSafety()
	if exob!=None:
		assert len(exob.subs)>0
		exob.setVerified()
		assert exob.verdepth<=self.getSafety()+pushes.lenchange()
	if safe == None: return
	pushes.conforms(safe)
def _dbgExit_dpush(self,pushes,exob,outp):
	pamt = pushes.lenchange()
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
		outp.setSafetyrow(None if safe == None else safe+pamt)
	else:
		safe = self.getSafety()
		outp.setSafety(None if safe == None else safe+pamt)
		outp.setVerified()

def _dbgEnter_pmultiline(self,context,out,indent,prepend,postpend,callback):
	if context.context!=None:
		if type(self) is TypeRow or type(self) is SubRow:
			self.setSafetyrow(len(context.context))
		else:
			self.setSafety(len(context.context))
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
		prep.setVerified()
		assert prep.verdepth<=limit
def _dbgExit_emptyinst(self,limit,mog,prep,ahjs):
	limadd = limit + (longcount(self) if type(mog) is bool and mog==False else 0)
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

	if extract != None:
		assert odsc != None
def _dbgEnter_flatten(self,delta,mog,assistmog,prep,obj,fillout):
	if prep != None:
		prep.setVerified()
	if obj != None:
		obj.setVerified()
		assert obj.verdepth<=self.verdepth+delta.lenchange()
		# obj.setSafety(self.getSafety())
	if prep!=None:
		assert prep.verdepth<=self.verdepth+delta.lenchange()#default to ==.
	self.setVerified()
	delta.conforms(self.getSafety())


	# self.setSafety(indesc.beginlen())#tried to flatten something not slotted for beginninglen.
def _dbgExit_flatten(self,delta,mog,assistmog,prep,obj,fillout,ahjs):
	if fillout == None:
		if then: ahjs,asdfasdf = ahjs
		passlen = 0 if prep==None else longcount(prep)
		ahjs.setSafety(self.getSafety()-passlen)
		# if obj != None and (obj.row!=0 or obj.column!=0):
		# 	for k in ahjs.flat:
		# 		assert k.obj.row!=0 or k.obj.column!=0
def _dbgEnter_verify(self,indesc,carry,reqtype,then):

	indesc.setSafety(0)
	self.setSafety(indesc.beginlen())#self is not slotted for indesc(begin) in verify
	if carry != None:
		carry.setVerified()
		carry.setSafety(len(indesc))#carry is not slotted for indesc(end) in verify

	if hasattr(self,'verdepth'): assert self.verdepth==None


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
		row = indesc.flat[(-indesc.postpushes).translate(outp.name)]
		outp.debugname = row.name



def htmlformat(struct,context,prepend,postpend="",tabs=0,forbidrange=None):
	a = []
	struct.pmultiline(FormatterObject(context,forhtml=True,forbidrange=forbidrange),a,tabs,prepend,postpend)
	return "<br>".join([j.replace("\t","&nbsp;&nbsp;&nbsp;&nbsp;").replace("<","&lt;").replace(">","&gt;").replace("::lt::","<").replace("::gt::",">") for j in a])

class TrackerError(Exception):
	pass
class DpushError(Exception):
	pass
class PreverifyError(Exception):
	pass
class LanguageError(Exception):
	def __init__(self,pos,message):
		Exception.__init__(self, message)
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

			# print(indesc)
			# print(len(indesc.flat))

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
class DelayedSub:
	def __init__(self,core,rows=None):
		self.core = core
		self.rows = ScopeDelta() if rows==None else rows
		if any(len(j)==3 for j in self.rows.pushes):
			self.core = self.core.dpush(self.rows)
			self.rows = ScopeDelta()
		self.isSubOb = self.core.isSubOb()


		dok = self.rows
		while type(self.isSubOb) is int and not dok.isempty():
			try:
				self.isSubOb = self.rows.translate(self.isSubOb)
			except DpushError:
				self.isSubOb = None
				break
			if type(self.isSubOb) is tuple:
				dok = self.isSubOb[1]
				self.isSubOb = self.isSubOb[0].isSubOb()
			else: break

		# if type(self.core) is RefTree and self.core.core==None and self.core.src==None and type(self.rows.translate(self.core.name)) is tuple:
		# 	self.core = self.core.dpush(self.rows)
		# 	self.rows = ScopeDelta()
	def dpush_ds(self,rows):
		return DelayedSub(self.core,self.rows+rows)

# the cure- six different ways

class ScopeDelta:
	def __init__(self,pushes=None):
		self.pushes = pushes if pushes !=None else []
		def _dbgTest():
			for j in self.pushes:
				if len(j)==2:
					assert type(j[0]) is int
					assert type(j[1]) is int
				elif len(j)==4:
					assert type(j[0]) is int
					assert type(j[1]) is int
					assert type(j[2]) is int
					assert type(j[3]) is int
				elif len(j)==3:
					assert type(j[0]) is int
					assert type(j[1]) is int
					assert type(j[2]) is list
				else:
					assert type(j[0]) is list
					for key,symbol in j[0]:
						assert symbol.verdepth<=key



	def __add__(self,other):
		return ScopeDelta(self.pushes+other.pushes)
	def __sub__(self,other):
		return self+(-other)
	def __neg__(self):
		res = []
		for j in reversed(self.pushes):
			if len(j)==2:
				res.append((-j[0],j[1]))
			elif len(j)==4:
				res.append((j[0],j[3],j[2]+j[3]-j[1],j[1]))
			else: assert False
		return ScopeDelta(res)
	def __repr__(self):
		return repr(self.pushes)
	def conforms(self,safe):
		for j in self.pushes:
			if len(j)==2:
				assert j[1]<=safe
				assert j[1]-j[0]<=safe
				safe+=j[0]
				assert type(j[0]) is int
				assert type(j[1]) is int
			elif len(j)==4:
				assert j[0]>=0
				assert j[1]>=0
				assert j[2]>=0
				assert j[3]>=0
				assert j[0]+j[1]<=j[2]
				assert j[2]+j[3]<=safe
				assert type(j[0]) is int
				assert type(j[1]) is int
				assert type(j[2]) is int
				assert type(j[3]) is int
			elif len(j)==3:
				assert j[1]<=safe
				assert j[1]-j[0]<=safe
				safe+=j[0]+len(j[2])
				assert type(j[0]) is int
				assert type(j[1]) is int
				assert type(j[2]) is list
			else:
				assert type(j[0]) is list
				for key,symbol in j[0]:
					if symbol.verdepth>key:
						print(key,symbol)
						assert symbol.verdepth<=key
	def isolate(self):
		return ScopeDelta(copy.copy(self.pushes))
	def isempty(self):
		return len(self.pushes)==0
	def append(self,next):
		self.pushes.append(next)
	def islowerbound(self,fug):
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==2:
				if fug>j[1]:
					if j[0]<0: return False
					fug+=j[0]
			elif len(j)==4:
				if   fug>j[0]: fug = j[2]+j[3]
			elif len(j)==3:
				if fug>=j[1]:
					return False
		return True


		# symbol.verdepth <= key
			# key is above you: key wont be hit.
			# key is beneath you: it'll sub out but the resultant stuff will all be beneath you anyway, so you continue onwards.



	def canTranslate(self,fug,ignoresubs=False):
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==2:
				if fug>=j[1]:
					fug+=j[0]
					if fug<j[1]: return False
			elif len(j)==4:
				if   fug>=j[0] and fug<j[0]+j[1]: fug+=j[2]-j[0]
				elif fug>=j[2] and fug<j[2]+j[3]: fug+=j[0]-j[2]
				elif fug>=j[0]+j[1] and fug<j[2]: fug+=j[3]-j[1]
			elif len(j)==3:
				if fug>=j[1]:
					if fug+j[0]<j[1]: return False
					fug+=j[0]+len(j[2])
			elif not ignoresubs:
				for key,symbol in j[0]:
					if fug==key:
						if ScopeDelta(self.pushes[i+1:]).islowerbound(key): return True
						return not symbol.detect(ScopeDelta(self.pushes[i+1:]))
		return True
	def translate(self,fug,ignoresubs=False):
		changefar = 0
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==2:
				changefar += j[0]
				if fug>=j[1]:
					fug+=j[0]
					if fug<j[1]: raise DpushError()
			elif len(j)==4:
				if   fug>=j[0] and fug<j[0]+j[1]: fug+=j[2]-j[0]
				elif fug>=j[2] and fug<j[2]+j[3]: fug+=j[0]-j[2]
				elif fug>=j[0]+j[1] and fug<j[2]: fug+=j[3]-j[1]
			elif len(j)==3:
				changefar += j[0]
				if fug>=j[1]:
					if fug+j[0]<j[1]: return (j[2],ScopeDelta(self.pushes[:i]),ScopeDelta(self.pushes[i+1:]))
					fug+=j[0]+len(j[2])
			elif not ignoresubs:
				for key,symbol in j[0]:
					if fug==key:
						return (symbol,ScopeDelta(self.pushes[i+1:]),fug,changefar)
			#teleport
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
		return sum(j[0] if len(j)==2 else j[0]+len(j[2]) for j in self.pushes if len(j)==2 or len(j)==3)

class FormatterObject:
	def __init__(self,context,magic=60,forhtml=False,forbidrange=None,littleeasier=True,colormap=None,fullrepresent=False,dependencies=None):
		self.magic = magic
		self.context = [k.name for k in context.flatnamespace()] if type(context) is ScopeObject else context
		self.forhtml = forhtml
		self.forbiddenrange = (forbidrange if forbidrange!=None else ScopeDelta()) - (context.prepushes+context.postpushes if type(context) is ScopeObject else ScopeDelta([]))#[] if forbidrange==None else forbidrange
		self.littleeasier = littleeasier
		self.colormap = {} if colormap==None else colormap
		self.fullrepresent = fullrepresent
		self.dependencies=dependencies if type(context) is not ScopeObject else [u[0] for u in context.oprows.dependencies]

	def getname(self,name):
		if type(name) is str:
			if self.forhtml: return "::lt::span style='color:#fdee73'::gt::"+name+"::lt::/span::gt::"
			return name
		if self.context == None: return str(name)
		if type(name) is int:
			if name<0:
				return self.dependencies[-1-name]
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
			colormap=dict([kv for kv in list(self.colormap.items())+[(index,color) for name,color,index in newbits]]),
			fullrepresent=self.fullrepresent,
			dependencies=self.dependencies
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

def implicitcast(indesc,expected,provided,obj,blame=None,soften=False,extract=None,thot=None,odsc=None,owner=None):
	if expected==None: return obj


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
					pp,obk = provided.origin
					for p in range(1,pA):
						pp,obi = pp.origin
						if type(pp) is RefTree: pp = pp.mangle_UE()
						obk = compose(obk,obi)
						pp=opp
					provob = buildfrom(obk,provided.flatten(ScopeDelta([]),[None]*len(provided.rows),obj=provob),provob.verdepth)

				if eA==0: return provob
				# print("beginning expected-side evaluation")

				pp,obk = expected.origin
				for e in range(1,eA):
					pp,obi = pp.origin
					if type(pp) is RefTree: pp = pp.mangle_UE()
					obk = compose(obk,obi)
					pp=opp

				guflat = headE.flatten(ScopeDelta([]),noneiflatten(obk),obj=provob)
				valid = True
				finob = []

				# print("guflat: ",guflat)

				moat = ScopeDelta()

				# vvleft = 0
				for h in range(len(expected.rows)):
					fou = extfind(h,obk)[0]
					if fou==None:
						valid = False
						break

					vv = longcount(expected.rows[h].name)

					inquestion = guflat.flat[fou].obj.dpush(ScopeDelta([(-fou,provob.verdepth)]))
					if expected.rows[h].obj==None:
						finob.append(SubRow(None,inquestion))
						# moat = moat + ScopeDelta([(longflattenunravel(expected.rows[h].name,expected.rows[h].type,inquestion,provob.verdepth)[0],),(-vv,provob.verdepth)])
					else:
						against = expected.rows[h].obj.dpush(moat)
						if not against.compare(inquestion,odsc,thot,extract):#<><><> make sure you aren't comparing things where they're set on both sides- that would be unesscesary.
							valid = False
							break
						# moat = moat + ScopeDelta([(longflattenunravel(expected.rows[h].name,expected.rows[h].type,expected.rows[h].obj,provob.verdepth)[0],),(-vv,provob.verdepth)])
					moat = moat + ScopeDelta([(longflattenunravel(expected.rows[h].name,expected.rows[h].type,inquestion,provob.verdepth)[0],),(-vv,provob.verdepth)])


				if valid: return SubsObject(finob,verdepth=provob.verdepth)
			if extract!=None:
				while st<len(extract): del extract[st]


			headP = headP.origin[0] if type(headP) is DualSubs and type(headE) is DualSubs and headP.origin!=None else None
			if type(headP) is RefTree: headP = headP.mangle_UE()
			pA += 1
		headE = headE.origin[0] if type(headE) is DualSubs and type(headE) is DualSubs and headE.origin!=None else None
		if type(headE) is RefTree: headE = headE.mangle_UE()
		eA += 1
	raise TypeMismatch(blame,expected,provided,indesc).soften(soften)

class ContextYam:
	def __init__(self,operators=None):
		self.operators = operators
		# self.lastComputation = lastComputation
		# self.nextComputation = Computation()

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
	# def sneakinsert(self,nflat,fillout):
	# 	def _dbgEnter():
	# 		self.setSafety(0)
	# 	def _dbgExit(ahjs):
	# 		ahjs.setSafety(0)
	# 	if len(nflat.flat) == 0: return self
	# 	return ScopeObject(self.flat[:fillout] + nflat.flat + [k.dpush(ScopeDelta([(len(nflat.flat),self.postpushes.translateGentle(fillout))])) for k in self.flat[fillout:]],self.prepushes+ScopeDelta([(len(nflat.flat),fillout)]),self.postpushes.pushchangethru(len(nflat.flat),fillout),self.oprows)


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
				if type(self.flat[i]) is TypeRow and type(self.flat[i].obj) is RefTree and self.flat[i].obj.src==None:
					cr1=(-self.postpushes).translate(self.flat[i].obj.name)
					assert (self.flat[i].obj.core==None) == (self.flat[cr1].obj==None)



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
	# def postpushPO(self,pushes):
	# 	if pushes.isempty(): return self
	# 	return ScopeObject(self.flat,self.prepushes,self.postpushes+pushes,self.oprows)
		# return res


	def beginlen(self):
		return len(self.flat) - self.prepushes.lenchange()
	def __len__(self):
		return len(self.flat) + self.postpushes.lenchange()


	def flatnamespace(self):
		# def _dbgEnter():
			# self.setSafety(0)
		def _dbgExit(ahjs):
			# ahjs.setSafety(0)
			assert len(ahjs) == len(self)
		databus = [TypeRow(k.name,None,k.obj) for k in self.flat]
		for amt,lim in self.postpushes.pushes:
			databus = databus[:lim]+databus[lim-amt:]
		return databus
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
				return (u_type(len(self)),u_type(len(self)))
			cr=self.postpushes.translateGentle(row)
			curr = self.flat[row].type.dpush(ScopeDelta([(len(self)-cr,min(cr,len(self)))]))
			bedoin,cuarg,ntype = curr.extractfibrationSubs(self,subs,minsafety=cosafety if type(name) is str else len(subs),maxsafety=safety,blame=pos)

			ntype = ntype.dpush(ScopeDelta([(-longcount(cuarg),len(self))]))


			drargs = SubsObject(cuarg.extractbetween(bedoin),verdepth=len(self))
			# assert len(drargs.subs) == len(bedoin)
			if not self.postpushes.canTranslate(row) or limiter!=None:
				obj = self.flat[row].obj.dpush(ScopeDelta([(len(self)-cr,min(cr,len(self)))]),exob=drargs if len(drargs.subs) else None)
				transferlines(obj,pos)
			elif self.flat[row].obj == None:
				obj = RefTree(cr,drargs,verdepth=len(self),pos=pos)
			else:
				obj = RefTree(
					cr,
					drargs,
					verdepth=len(self),
					pos=pos,
					core=DelayedSub(self.flat[row].obj,ScopeDelta([(len(self)-cr,min(cr,len(self)))]))
				)
			return (obj,ntype)

		if len(self.flat) == 0:
			return (u_type(verdepth=len(self)),u_type(verdepth=len(self))) if reqtype else u_type(verdepth=len(self))

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


	def writefile(self,file):
		if self.name==None:
			if self.obj!=None:
				file.writeChar("c")
				self.type.writefile(file)
				self.obj.writefile(file)
			elif self.silent==None or not self.silent["silent"]:
				file.writeChar("a")
				self.type.writefile(file)
			else:
				file.writeChar("b")
				self.type.writefile(file)
		else:
			if self.obj!=None:
				file.writeChar("f")
				file.writeStrInc(self.name)
				self.type.writefile(file)
				self.obj.writefile(file)
			elif self.silent==None or not self.silent["silent"]:
				file.writeChar("d")
				file.writeStrInc(self.name)
				self.type.writefile(file)
			else:
				file.writeChar("e")
				file.writeStrInc(self.name)
				self.type.writefile(file)


	def toJSON(self):
		return {
			"name":self.name,
			"cent":self.type.toJSON(),
			"obj":None if self.obj==None else self.obj.toJSON(),
			"silent":self.silent
		}

	# def ddpush(self,amt,lim,repls=None,replsrc=None):
	# 	return TypeRow(self.name,self.type.ddpush(amt,lim,repls,replsrc),None if self.obj == None else self.obj.ddpush(amt,lim,repls,replsrc),self.silent)
	def detect(self,ranges):
		return self.type.detect(ranges) or self.obj!=None and self.obj.detect(ranges)


	def dpush(self,pushes):
		"""dbg_ignore"""
		return TypeRow(self.name,self.type.dpush(pushes),None if self.obj == None else self.obj.dpush(pushes),self.silent)
	# def spush(self,pushes):
	# 	"""dbg_ignore"""
	# 	return TypeRow(self.name,self.type.dpush(pushes),None if self.obj == None else self.obj.dpush(pushes),self.silent)



	def vershortcut(self,indesc):
		return TypeRow(self.name,self.type.verify(indesc),None if self.obj == None else self.obj.verify(indesc),self.silent)
	

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
	# def ddpush(self,amt,lim,repls=None,replsrc=None):
	# 	return SubRow(self.name,self.obj.ddpush(amt,lim,repls,replsrc))
	def detect(self,ranges):
		return self.obj.detect(ranges)
	def dpush(self,pushes):
		"""dbg_ignore"""
		return SubRow(self.name,self.obj.dpush(pushes))
	# def spush(self,pushes):
	# 	"""dbg_ignore"""
	# 	return SubRow(self.name,self.obj.dpush(pushes))


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
	def isemptytype(self):
		return False
	def fulavail(self):
		raise InvalidSplit()
	def setVerified(self):
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

	def flatten(self,delta,mog,assistmog=None,prep=None,obj=None,fillout=None,then=False):
		if type(mog) is list:
			if type(self) is RefTree:
				yap = self.mangle_UE()
				if yap!=None: return yap.flatten(delta,mog,assistmog,prep,obj,fillout,then)
			raise InvalidSplit()

		yatta = self.verdepth+delta.lenchange()

		if prep != None: njprep = prep.dpush(ScopeDelta([(yatta-(longcount(prep) if prep!=None else 0)-prep.verdepth,prep.verdepth)]))
		pushob = None if obj==None else obj.dpush(ScopeDelta([(yatta-obj.verdepth,obj.verdepth)]))
		if prep == None or len(njprep.rows)==0:
			outp = ScopeObject([TypeRow(mog,self.dpush(delta),None if pushob == None else pushob)])
		else:
			outp = ScopeObject([TypeRow(mog,self.dpush(delta).addfibration(njprep),None if pushob == None else pushob.addlambdas(njprep))])
		if then: return (outp,delta)
		return outp
	def isemptyinst(self,si,prep=None):
		return False
	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not int: raise InvalidSplit()
		prep = None if prep == None else prep.dpush(ScopeDelta([(limit-prep.verdepth,prep.verdepth)]))

		return RefTree(name=mog,args=prep,verdepth=limit)
	def addfibration(self,args,pos=None):
		shaz = longcount(args)
		if len(args) == 0:
			return self.dpush(ScopeDelta([(-shaz,self.verdepth-shaz)]))
		return Strategy(args,self,verdepth=self.verdepth-shaz,pos=self if pos==None else pos)
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
				if not self.args.subs[len(self.args.subs)-1-elim].obj.isemptyinst(striphuman(ndepth,si[len(si)-1-elim])[0]): break
				thisdepth = longcount(si[len(si)-elim-1])
				valid = True
				if self.src!=None:
					if self.src.detect(ScopeDelta([(-thisdepth,ndepth)])): 
						valid = False
				for k in self.args.subs[:len(self.args.subs)-1-elim]:
					if k.obj.detect(ScopeDelta([(-thisdepth,ndepth)])):
						valid = False
						break
				if not valid: break
				elim+=1
			if elim:
				ndepth = starter+longcount(si[:len(si)-elim])
				stretch = ScopeDelta([(ndepth-fafter,ndepth)])
				nsubs = SubsObject([k.dpush(stretch) for k in self.args.subs[:len(self.args.subs)-elim]],verdepth=ndepth)
				core = None
				if self.core != None:
					core = self.core.dpush_ds(stretch)
				outp = RefTree(self.name,nsubs,None if self.src==None else self.src.dpush(stretch),verdepth=ndepth,pos=self,core=core)
		if type(self) is Lambda:
			return Lambda(si[:len(si)-elim]+self.si,self.obj,verdepth=starter,pos=self if pos==None else pos)
		if len(si)==elim: return outp
		return Lambda(si[:len(si)-elim],outp,verdepth=starter,pos=self if pos==None else pos)
	def extractfibration(self,indesc,si,blame=None):
		if len(si)==0: return (DualSubs(verdepth=self.verdepth),self)
		try:
			carry = self.trimallnonessential(si) if type(self) is Strategy else self
		except InvalidSplit as u:
			u.reblame(blame,self.args,si,indesc)
			raise u
		ac = []
		while len(si)>len(ac):
			if type(carry) is RefTree:
				mogo = carry.mangle_FE()
				if mogo!=None: carry = mogo
			if type(carry) is not Strategy:
				raise NonLambdaTypeError(blame,self,indesc)
			ac = ac + carry.args.rows
			carry = carry.type
		advdepth = self.verdepth+longcount([a.name for a in ac[:len(si)]])
		if len(si)<len(ac):
			carry = carry.addfibration(DualSubs(ac[len(si):],verdepth=advdepth))
			ac = ac[:len(si)]
		return (DualSubs(ac,verdepth=self.verdepth),carry)

	def extractfibrationSubs(self,indesc,si,minsafety=None,maxsafety=None,blame=None):

		if len(si)==0: return (DualSubs(verdepth=self.verdepth),DualSubs(verdepth=self.verdepth),self)
		try:
			carry = self.trimallnonessential() if type(self) is Strategy else self
		except InvalidSplit as u:
			u.reblame(blame,self.args,si,indesc)
			raise u
		nindesc = indesc
		ndelta = ScopeDelta([])
		inflow = si
		ac = []
		dc = []
		earlyabort = True
		while len(inflow):

			advdepth = self.verdepth+longcount([a.name for a in ac])

			goneonce=False
			asgo = []
			# midflow = []
			while True:
				if type(carry) is RefTree:
					mogo = carry.mangle_FE()
					if mogo!=None: carry = mogo
				if type(carry) is not Strategy: break
				goneonce=True
				# preserve alts on mangle?

				oflow = []
				asgo = asgo + carry.args.rows
				midflow = DualSubs(asgo,verdepth=advdepth).compacassign(inflow,oflow,minsafety,maxsafety) #<><>rethink safeties...<><>
				# inflow = oflow
				carry = carry.type
				if not len(oflow): break


			if not goneonce: raise VariableAssignmentError(blame,inflow[0][0])
			(dbdbdb,earlyabort),(nindesc,ndelta) = DualSubs(asgo,verdepth=advdepth).peelcompactify(nindesc,midflow,then=True,earlyabort=earlyabort,epo=ndelta)
			if any(k.obj==None for k in dc): raise LanguageError(blame,"Hole in arguments list")

			if minsafety!=None: minsafety -= len(asgo)
			if maxsafety!=None: maxsafety -= len(asgo)
			gc = longcount([k.name for k in asgo])
			pob = ScopeDelta([(gc,len(nindesc)-gc)])
			# nindesc = nindesc.prepushPR(pob)


			#<><> might be able to make inflow depth-agnostic
			inflow = [(o[0],(o[1][0] if o[1][1]==False else o[1][0].dpush(pob),o[1][1] if type(o[1][1]) is bool else o[1][1].dpush(pob))) for o in oflow]

			ac = ac + asgo
			dc = dc + dbdbdb.rows
			carry = carry.dpush(ndelta)

		lensi = 0
		while lensi<len(dc) and dc[lensi].obj!=None:lensi+=1
		advdepth = self.verdepth+longcount([a.name for a in ac[:lensi]])
		if lensi<len(ac):
			carry = carry.addfibration(DualSubs(dc[lensi:],verdepth=advdepth))
			ac = ac[:lensi]
			dc = dc[:lensi]
		return (DualSubs(ac,verdepth=self.verdepth),DualSubs(dc,verdepth=self.verdepth),carry)



	def reference(self,s):
		if type(self) is SubsObject: return self.subs[s].obj
		elif type(self) is Lambda and type(self.obj) is SubsObject: return Lambda(self.si,self.obj.subs[s].obj,verdepth=self.verdepth,pos=self)
		elif type(self) is RefTree and self.core!=None and type(self.core.isSubOb) is bool and self.core.isSubOb:
			self = self.unwrap()
			if type(self) is SubsObject: return self.subs[s].obj
			elif type(self) is Lambda and type(self.obj) is SubsObject: return Lambda(self.si,self.obj.subs[s].obj,verdepth=self.verdepth,pos=self)
			assert False
		return RefTree(src=self,name=s,verdepth=self.verdepth,pos=self)



	def __repr__(self):
		return self.prepr(FormatterObject(None))




	def isSubOb(self):
		if type(self) is SubsObject: return True
		if type(self) is Lambda and type(self.obj) is SubsObject: return True
		if type(self) is RefTree and self.core!=None: return self.core.isSubOb
		if type(self) is RefTree: return self.name
		return False


def initTobj(F):
	indbg=[False]
	def _dbgTest():
		indbg[0]=True

	def wrapper(self,*args,**kwargs):
		"""dbg_ignore"""
		# if 'src' not in kwargs: pos = None
		# self.altversion = [] if altversion==None else altversion
		# self.verdepth = None
		# self.complexity = 0
		# self.PJID = None
		F(self,*args,**kwargs)
		if "verdepth" in kwargs:
			# for alt in self.altversion:
			# 	self.touches.update(alt.touches)

			# def _dbgTest():
			# for alt in self.altversion: assert alt.verdepth == self.verdepth
			self.setSafety(self.verdepth)
			# for k in self.touches:
			# 	assert k==0 or k<self.verdepth
			# for alt in self.altversion:
			# 	if alt.softtouches==self.softtouches:
			# 		assert False

	if indbg[0]: return wrapper
	return F
def coflattenunravel(si,ob,left):
	if type(si) is list:
		res = []
		for n in range(len(si)):
			res = res + coflattenunravel(si[n],ob.reference(n),left+len(res))
		return res
	return [(left,ob)]
def longflattenunravel(si,ty,ob,left):
	if type(si) is list:
		ty = ty.type if type(ty) is Strategy else ty
		s = 0
		res = []
		for k in range(len(si)):
			if ty.rows[k].obj==None:
				ui,left = longflattenunravel(si[k],ty.rows[k].type,ob.reference(s),left)
				res = res + ui
				s+=1
			else:
				left += longcount(si[k])
		return (res,left)
	return ([(left,ob)],left+1)
def lazyflatten(F):
	def wrapper(self,delta,mog=False,assistmog=None,prep=None,obj=None,fillout=None,then=False):
		"""dbg_ignore"""



		if type(mog) is not list and type(mog) is not bool: return Tobj.flatten(self,delta,mog,assistmog,prep,obj,fillout=fillout,then=then)

		sel1 = self.mangle_UE() if type(self) is RefTree else self
		sel = sel1 if type(sel1) is DualSubs else sel1.type if type(sel1) is Strategy else None
		if type(mog) is bool and mog == False: mog = sel.fulavail()


		if len(sel.fulavail()) != len(mog):
			raise InvalidSplit()
		if assistmog == None:
			assistmog,ext = striphuman(self.verdepth,mog)
			fillout = self.verdepth

		return F(sel1,delta,mog,assistmog,prep,obj,fillout,then=then)
	return wrapper

class DualSubs(Tobj):
	@initTobj
	def __init__(self,rows=None,verdepth=None,origin=None,pos=None):
		self.rows = rows if rows != None else []
		self.origin = origin
		self.verdepth = verdepth
		transferlines(self,pos)
		# if verdepth!=None:
		# 	self.verdepth = verdepth
		# 	self.touches = set()
		# 	self.softtouches = set()
		# 	self.complexity = 1
		# 	for sub in self.rows:
		# 		assert type(sub) is TypeRow#safemode
		# 		self.touches.update(sub.type.touches)
		# 		self.softtouches.update(sub.type.softtouches)
		# 		self.complexity+=sub.type.complexity
		# 		if sub.obj!=None:
		# 			self.touches.update(sub.obj.touches)
		# 			self.softtouches.update(sub.obj.softtouches)
		# 			self.complexity+=sub.obj.complexity
		# 	self.touches = {k for k in self.touches if k<verdepth}
		# 	self.softtouches = {k for k in self.softtouches if k<verdepth}

	def extractbetween(self,older):
		for j in self.rows: assert j.obj != None
		cuu = []
		left = 0
		for g in range(len(self.rows)):
			if older.rows[g].obj == None:
				cuu.append(SubRow(None,self.rows[g].obj.dpush(ScopeDelta([(-left,self.verdepth)]))))
			left += longcount(older.rows[g].name)
		return cuu

	def isemptytype(self):
		return len(self)==0


	def writefile(self,file,shutup=False):
		if not shutup:
			if self.origin==None: file.writeChar("C")
			else:
				file.writeChar("D")
				self.origin[0].writefile(file)
				file.writeNumInc(self.origin[1])
		file.writeNum(len(self.rows))
		for j in self.rows:
			j.writefile(file)

	def primToJSON(self):
		return (
			"DualSubs",#"type":
			[k.PJID for k in self.rows]#"rows":
		)
	def toJSON(self):
		return {
			"type":"DualSubs",
			"rows":[k.toJSON() for k in self.rows],
			"origin":None if self.origin==None else {"parent":self.origin[0].toJSON(),"map":self.origin[1]},
		}
	def prepr(self,context):
		yud = []
		for k in self.rows:
			word = context.newcolors(k.name)
			yud.append(k.prepr(context,word=word))
			context = context.addbits(word)
		return context.red("{")+",".join(yud)+context.red("}")
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		pmultilinecsv(context,out,indent,self.rows,prepend+context.red("{"),context.red("}")+postpend,lamadapt=lambda x:x.name,callback=callback,delim=context.red(","))

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

	def dpush(self,pushes,exob=None,disgrace=None):
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
		return DualSubs(cu,verdepth=self.verdepth+pushes.lenchange(),origin=None if self.origin==None else (self.origin[0].dpush(pushes),self.origin[1]),pos=self)

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
	def trimallnonessential(self,si=None,disgrace=None,alsokill=None):
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
					myu = m.type
					if type(myu) is RefTree: myu = myu.mangle_UE()
					if type(myu) is DualSubs:
						left = unshift(left,myu.rows,self.rows[k].name,si[s])
						kaname = copy.copy(m.name)
						restype = myu.trimallnonessential(si[s],alsokill=kaname)
						m = TypeRow(kaname,restype,m.obj,m.silent)
					elif type(myu) is not Strategy: raise InvalidSplit()
					else:
						mot = myu.type
						if type(mot) is RefTree: mot = mot.mangle_UE()
						if type(mot) is DualSubs:
							left = unshift(left,mot.rows,self.rows[k].name,si[s])
							kaname = copy.copy(m.name)
							restype = Strategy(myu.args,mot.trimallnonessential(si[s],alsokill=kaname),verdepth=myu.verdepth)
							m = TypeRow(kaname,restype,m.obj,m.silent)
						else: raise InvalidSplit()
				else:
					left += longcount(self.rows[k].name)
				cu.append(m)
				s += 1
			else:
				if alsokill!=None: del alsokill[s]
				disgrace.append((-longcount(self.rows[k].name),self.verdepth+left))
		return DualSubs(cu,verdepth=self.verdepth)
	@lazyflatten
	def flatten(self,delta,mog,assistmog,prep=None,obj=None,fillout=None,then=False):
		s = 0
		cu = ScopeObject()
		left = self.verdepth + delta.lenchange()
		for n in range(len(self.rows)):
			nobj = None
			if self.rows[n].obj != None:
				nobj = self.rows[n].obj.dpush(delta)
			else:
				if obj != None:
					nobj = obj.reference(s)
				s+=1
			nflat = self.rows[n].type.flatten(delta,mog[n],assistmog[n],prep,obj=nobj,fillout=fillout)
			cu.flat += nflat.flat
			vv = longcount(self.rows[n].name)
			if conservativeeq(self.rows[n].name,mog[n]) and prep == None:
				if nobj!=None:
					jaaj = longflattenunravel(self.rows[n].name,self.rows[n].type,nobj,left)
					delta = delta + ScopeDelta([(jaaj[0],)])
				left += vv
			else:
				delta = delta + ScopeDelta([(len(nflat.flat),fillout)])
				left += len(nflat.flat)
				if nobj == None:
					dbgdbg = left
					passprep = prep.emptyinst(dbgdbg,striphuman(dbgdbg-longcount(prep),prep.fulavail())[0]) if prep != None else None
					nobj = self.rows[n].type.emptyinst(dbgdbg,assistmog[n],prep=passprep)
				jaaj = longflattenunravel(self.rows[n].name,self.rows[n].type,nobj,left)
				delta = delta + ScopeDelta([(jaaj[0],),(-vv,left)])
			fillout = fillout + len(nflat.flat)

		return (cu,delta) if then else cu
	def emptyinst(self,limit,mog=False,prep=None):
		if mog == False: mog,limit = striphuman(limit,self.fulavail())
		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)
		assert len(self.rows) == len(mog)
		mog = [mog[i] for i in range(len(mog)) if self.rows[i].obj == None]
		return SubsObject([SubRow(None,self[k].emptyinst(limit,mog[k],prep)) for k in range(len(self))],verdepth=limit)
	def needscarry(self):
		return False
	
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assertstatequal(indesc,self,carry,u_type(len(indesc)))
		outs = []
		oidns = indesc
		bi = len(indesc)
		for n in range(len(self.rows)):
			if self.rows[n].type == None:
				obj,nty = self.rows[n].obj.verify(indesc,reqtype=True)
			elif type(self.rows[n].type) is Strategy:

				gnoa,ndsid = self.rows[n].type.args.verify(indesc,then=True)
				if self.rows[n].type.type == None:
					obj,nty = self.rows[n].obj.verify(ndsid,reqtype=True)
				else:
					nty = self.rows[n].type.type.verify(ndsid,u_type(len(ndsid)))
					obj = self.rows[n].obj.verify(ndsid,nty) if self.rows[n].obj!=None else None

				nty = Strategy(gnoa,nty,verdepth=len(indesc))

				if obj!=None:
					despar = ScopeDelta()
					gnoa.trimallnonessential(None,despar)
					if not despar.isempty(): obj = obj.dpush(despar)
					obj = Lambda(gnoa.semavail(),obj,verdepth=len(indesc),pos=obj)
			else:
				nty = self.rows[n].type.verify(indesc,u_type(len(indesc)))
				obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None


			try:
				if self.rows[n].name == "*****":
					if type(nty) is RefTree:
						uwa = nty.mangle_UE()
						if uwa==None: raise InvalidSplit()
						self.rows[n].name = uwa.fulavail()
					else: self.rows[n].name = nty.fulavail()

				vertype = TypeRow(self.rows[n].name,nty,obj if obj!=None else SubsObject(verdepth=len(indesc)) if nty.isemptytype() else None,self.rows[n].silent)
				outs.append(vertype)

				if type(self.rows[n].name) is not list:
					indesc = indesc.addflat(ScopeObject([vertype]))
				else:
					indesc = indesc.addflat(nty.flatten(ScopeDelta([]),self.rows[n].name,obj=vertype.obj))
			except InvalidSplit as u:
				u.reblame(self,nty,self.rows[n].name,indesc)
				raise u

		outp = DualSubs(outs,pos=self,verdepth=bi)
		return (outp,indesc) if then else (outp,u_type(bi)) if reqtype else outp
	def peelcompactify(self,indesc,compyoks,then=False,earlyabort=True,epo=None):
		def _dbgEnter():
			indesc.setSafety(0)
			assert type(compyoks) is list
			for j in compyoks:
				assert type(j) is tuple and (len(j) == 3 or len(j)==4)
				if j[2]==False:
					j[1].setSafety(indesc.beginlen())
				else:
					j[1].setSafety(len(indesc))
		# def _dbgExit(outp):
		# 	if outp != None:
		# 		if then:
		# 			outp,ninds = outp
		# 			assert type(ninds) is ScopeObject
		# 			ninds.setSafety(0)
		# 		outp,early = outp
		# 		assert type(early) is bool
		# 		assert type(outp) is DualSubs
		# 		outp.setVerified()
		# 		outp.setSafety(len(indesc))

		for y in range(len(compyoks)):
			if len(compyoks[y])>3:
				compyoks[y] = (compyoks[y][0],compyoks[y][1],compyoks[y][2])
		return self.compacrecurse(compyoks,[],[],indesc,ScopeDelta([]) if epo==None else epo,then=then,earlyabort=earlyabort)

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
				if safety != None and s < safety:
					raise VariableAssignmentError(inyoks[s][1][0],inyoks[s][0])
				overflow.append(inyoks[s])
			else:
				yoks.append((nan,inyoks[s][1][0],inyoks[s][1][1]))
		return yoks
	def compacrecurse(self,yoks,trail,prep,indesc,delta,then=False,earlyabort=False):
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
			if len(outp)==3:
				ming,reassembled,earlyabort = outp
				return
			elif then:
				outp,(ninds,ndelt) = outp
				assert type(ninds) is ScopeObject
				assert type(ndelt) is ScopeDelta
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

		startindesc = indesc
		startdelta = delta
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
			reassembled = DualSubs(cu + [self.rows[b] for b in range(n,len(self.rows))],verdepth=self.verdepth)
			if trail == ming[:len(trail)]:
				yoob = reassembled.compacrecurse(yoks,trail,prep,startindesc,startdelta,then=then,earlyabort=earlyabort)
				return yoob
			yoob = (ming,reassembled,earlyabort)
			return yoob

		def namerical(lim,names,sof):
			if type(names) is not list: return [(lim,sof)]
			i = []
			for j in range(len(names)):
				i = i+namerical(lim+len(i),names[j],sof+[j])
			return i
		thot = prep
		for n in range(len(self.rows)):
			row = self.rows[n]
			rowtype = row.type.dpush(delta)
			if self.rows[n].obj != None:
				obj = self.rows[n].obj.dpush(delta) 
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

									obj = implicitcast(indesc,rowtype,othertype,obj,blame=yoks[k][1],soften=earlyabort,extract=yoks,thot=thot,odsc=lencom1,owner=trail+[n])

									ming = getming(thot,st)
									if ming!=None: return restart(thot,ming)
								else:
									obj = yoks[k][1].dpush(ScopeDelta([(lentho,lencom1)]))
								if rowtype.detect(ScopeDelta([(-lentho,lencom1)])):

									raise CouldNotDeduceType(yoks[k][1]).soften(earlyabort)
								break
							if rowtype.detect(ScopeDelta([(-lentho,lencom1)])):
								if type(yoks[k][1]) is Lambda and not yoks[k][1].obj.needscarry():
									try:
										truncargs,ntype = rowtype.extractfibration(indesc,yoks[k][1].si,blame=yoks[k][1])
									except InvalidSplit as u:
										raise u.soften(earlyabort)
									if not lentho or not truncargs.detect(ScopeDelta([(-lentho,lencom1)])):
										# if yoks[k][1].si==["w"]:
										# 	print("found the bad example.")
										# 	print([(-lentho,lencom1)])
										# 	print(cu)
										# 	print(yoks)
										# 	print(delta)
										# 	print(truncargs.prepr(FormatterObject(None,fullrepresent=True)))
										# 	print(ntype.prepr(FormatterObject(None,fullrepresent=True)))
										yasat = truncargs.dpush(ScopeDelta([(-lentho,lencom1)])) if lentho else truncargs
										earlyabort = False
										yasatflat = yasat.flatten(ScopeDelta([]),yoks[k][1].si)
										obj,ntyp = yoks[k][1].obj.verify(indesc.trimabsolute(len(thot)).addflat(yasatflat),reqtype=True)
										obj  =  obj.addlambdasphase2(yoks[k][1].si,pos=yoks[k][1])
										ntyp = ntyp.addfibration(yasat)
										# print("assigned: ",row.name)
										# print("assigned: ",indesc.flat[len(indesc.flat)-lentho-1+yoks[k][0][0]])
										yoks[k] = (yoks[k][0],obj,ntyp)
										st = len(yoks)
										obj  =  obj.dpush(ScopeDelta([(lentho,lencom1)]))
										ntyp = ntyp.dpush(ScopeDelta([(lentho,lencom1)]))
										obj = implicitcast(indesc,rowtype,ntyp,obj,blame=yoks[k][1],soften=earlyabort,extract=yoks,thot=thot,odsc=lencom1,owner=trail+[n])
										ming = getming(thot,st)
										if ming!=None: return restart(thot,ming)
										# if rowtype.detect(ScopeDelta([(-lentho,lencom1)])): 
										raise CouldNotDeduceType(yoks[k][1]).soften(earlyabort)
										# break
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
				moro = rowtype.compacrecurse(yoks,trail+[n],thot,indesc,delta,then=False,earlyabort=earlyabort)
				if len(moro)==3:#this is broken...?????
					ming,moro,earlyabort = moro
					obj = SubsObject(verdepth=len(indesc)) if moro.isemptytype() else None
					cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
					reassembled = DualSubs(cu+[self.rows[j] for j in range(n+1,len(self.rows))],verdepth=self.verdepth)
					if trail == ming[:len(trail)]:
						return reassembled.compacrecurse(yoks,trail,prep,startindesc,startdelta,then=then,earlyabort=earlyabort)
					return (ming,reassembled,earlyabort)
				moro,earlyabort = moro
				obj = SubsObject(verdepth=len(indesc)) if moro.isemptytype() else None
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				cu.append(TypeRow(row.name,rowtype,obj,self.rows[n].silent))
			thot = thot+namerical(len(indesc),self.rows[n].name,trail+[n])
			if type(self.rows[n].name) is not list:
				insf = TypeRow(self.rows[n].name,rowtype,obj,self.rows[n].silent)
				if obj!=None: delta = delta + ScopeDelta([([(len(indesc),obj)],)])
				indesc = indesc.sneakadd(ScopeObject([insf]))
			else:
				if obj!=None: delta = delta + ScopeDelta([(longflattenunravel(self.rows[n].name,rowtype,obj,len(indesc))[0],)])
				indesc = indesc.sneakadd(self.rows[n].type.flatten(ScopeDelta([]),self.rows[n].name,obj=obj))
		for n in range(len(self.rows)):
			for yok in yoks:
				if yok[0] == trail+[n] and cu[n].obj==None:
					raise CouldNotDeduceType(yok[1]).addparameterdata(yoks,trail+[n],len(thot),None,indesc).soften(earlyabort)
					# raise LanguageError(yok[1],"Cannot infer type of parameter.")
		outp = DualSubs(cu,verdepth=self.verdepth,pos=self)
		return ((outp,earlyabort),(indesc,delta)) if then else (outp,earlyabort)

	def applytemplate(self,indesc,NSC,subs,rows,blame=None,shortname=None):
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

		wlist = self.flatten(ScopeDelta([]),NANms).flat
		wonk = indesc.addflat(ScopeObject(wlist)).prepushPR(ScopeDelta([(1,indesc.beginlen()+n) for n in range(len(wlist)) if not inc[n]]))

		jmore = DualSubs(rows,pos=blame).verify(wonk).flatten(ScopeDelta([])).flat

		wclist = [((wlist+jmore)[d],(inc+[True for j in jmore])[d],self.verdepth+d,[]) for d in range(len(inc)+len(jmore))]
		for a in range(len(wclist)):
			for b in reversed(range(a)):
				if self.verdepth+b not in wclist[a][3] and wclist[b][0].obj==None and wclist[a][0].detect(ScopeDelta([(-1,self.verdepth+b)])):
					wclist[a][3].append(self.verdepth+b)
					for c in wclist[b][3]:
						if c not in wclist[a][3]: wclist[a][3].append(c)

		dn = copy.copy(subs)
		while len(dn):
			if dn[0].name!=None and dn[0].name[0] in dn: continue
			for origindex in range(len(wclist)):
				a=0
				while wclist[a][2]!=origindex+self.verdepth: a+=1
				if wclist[a][0].obj==None and dn[0].name==None or dn[0].name[0]==wclist[a][0].name:
					# everything without a ref | everything with a ref.
					tub = []
					wlist = []
					sources = []
					for b in range(len(wclist)):
						if b!=a and wclist[a][2] not in wclist[b][3]:
							wlist.append((wclist[b][0].dpush(ScopeDelta(tub)),wclist[b][1],wclist[b][2],wclist[b][3]))
							sources.append(b)
						else:
							tub.insert(0,(-1,self.verdepth+b))
					wonk = indesc.addflat(ScopeObject([w[0] for w in wlist])).prepushPR(ScopeDelta([(1,indesc.beginlen()+n) for n in range(len(wlist)) if not wlist[n][1]]))
					ltype = wclist[a][0].type.dpush(ScopeDelta([(len(wlist)-a,self.verdepth+a)]))

					typenotchange = dn[0].name==None or len(dn[0].name)==1

					if typenotchange:
						yarn = TypeRow(wclist[a][0].name,ltype,dn[0].obj.verify(wonk,ltype),wclist[a][0].silent)
						del dn[0]
					else:
						if type(wclist[a][0]) is not DualSubs: raise LanguageError(blame,"Tried to subaccess thing that doesn't have subproperties "+str(dn[0].name))
						desc = []
						for o in reversed(range(len(dn))):
							if dn[o].name!=None and dn[o].name[0]==wclist[a][0].name and len(dn[o]).name>1:
								desc.append(dn[o])
								del dn[o]
						yarn = TypeRow(wclist[a][0].name,ltype.applytemplate(wonk,([],[]),desc,[],blame=blame),None,wclist[a][0].silent)
					
					# everything A refs | A | everything else
					# everything A refs: [first half only has elements dropped, second half only has elements dropped] (like first range subset, but even more are dropped.)
					# A: [introductions and drops, no swaps]
					# everything else: [lots of swaps, no drops, some introduced]

					#everything else needs a depth switch? (yes) (previous elements have been rearranged.)

					hs = self.verdepth
					for b in sources:
						if wclist[b][2] not in wclist[a][3] and wclist[a][2] not in wclist[b][3]:
							if wclist[b][0].obj==None and (yarn.obj if typenotchange else yarn.type).detect(ScopeDelta([(-1,hs)])):
								wclist[a][3].append(wclist[b][2])
								for c in wclist[b][3]:
									if c not in wclist[a][3]: wclist[a][3].append(c)
								for c in range(len(wclist)):
									if wclist[a][2] in wclist[c][3]:
										for d in wclist[a][3]:
											if d not in wclist[c][3]: wclist[c][3].append(d)
						hs+=1

					wlist.append((yarn,wclist[a][1],wclist[a][2],wclist[a][3]))
					sources.append(a)

					for b in range(len(wclist)):
						if a!=b and b not in sources: sources.append(b)

					if typenotchange:
						converter = ScopeDelta([
							([(len(indesc)+b,yarn.obj)],)
						])
					else:
						converter = ScopeDelta([
							(1,len(indesc)+b),
							([(
								len(indesc)+b+1,
								implicitcast(
									None,
									ltype,
									yarn.type,
									RefTree(self.verdepth+b,verdepth=self.verdepth+b+1)
								)
							)],),
							(-1,len(indesc)+b+1)
						])

					for b in range(len(wlist),len(wclist)):
						tub1 = []
						tub2 = []
						tub3 = []
						for c in range(b):
							if sources[b]<sources[c]:
								tub1.append((1,self.verdepth+c))
						for c in sources[b+1:]:
							if sources[b]>c:
								tub2.append((-1,self.verdepth+c))
						hacakewalk = copy.copy(sources)
						for c in range(b):
							for d in range(c):
								if hacakewalk[c]<hacakewalk[d] and hacakewalk[d]<hacakewalk[b]:
									tub3.append((self.verdepth+hacakewalk[c],1,self.verdepth+hacakewalk[d],1))
									swp = hacakewalk[c]
									hacakewalk[c] = hacakewalk[d]
									hacakewalk[d] = swp
						tub = tub3+sorted(tub2,key=lambda x:-x[1])+sorted(tub1,key=lambda x:x[1])
						wlist.append((wclist[sources[b]][0].dpush(ScopeDelta(tub)+converter),wclist[sources[b]][1],wclist[sources[b]][2],wclist[sources[b]][3]))
					wclist=wlist
					break
			else:
				raise VariableAssignmentError(blame,dn[0].name[0])

		def unlongcount(si,map,lc=0):
			if type(si) is list:
				res = []
				for i in si:
					k,lc = unlongcount(i,map,lc)
					res.append(k)
				return (res,lc)
			for i in range(len(map)):
				if map[i]==self.verdepth+lc: return (i,lc+1)
			assert False

		return DualSubs([i[0] for i in wclist],verdepth=self.verdepth,pos=blame,origin=(shortname if shortname!=None else self,unlongcount(NANms,[i[2] for i in wclist])[0]))
class SubsObject(Tobj):
	@initTobj
	def __init__(self,subs=None,verdepth=None,pos=None):
		# def _dbgEnter():
		# 	for sub in subs:
		# 		assert type(sub) is SubRow
		self.subs = subs if subs != None else []
		self.verdepth = verdepth
		transferlines(self,pos)
		# if verdepth!=None:
		# 	self.touches = set()
		# 	self.softtouches = set()
		# 	self.verdepth = verdepth
		# 	self.complexity = 1
		# 	for sub in self.subs:
		# 		assert type(sub) is SubRow#safemode
		# 		self.touches.update(sub.obj.touches)
		# 		self.softtouches.update(sub.obj.softtouches)
		# 		self.complexity += sub.obj.complexity


	def writefile(self,file,shutup=False):
		if not shutup: file.writeChar("F")
		file.writeNum(len(self.subs))
		for j in self.subs:
			j.obj.writefile(file)


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
	def prepr(self,context):
		res = context.red("(")+",".join([k.prepr(context) for k in self.subs])+context.red(")")
		return res
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		pmultilinecsv(context,out,indent,self.subs,prepend+context.red("("),context.red(")")+postpend,callback=callback)

	def isemptyinst(self,si,prep=None):
		if type(si) is not list: return False
		if len(si)!=len(self.subs): return False
		return all(self.subs[k].obj.isemptyinst(si[k],prep=prep) for k in range(len(si)))

	def detect(self,ranges):
		return any(sub.detect(ranges) for sub in self.subs)

	def dpush(self,pushes,exob=None):
		return SubsObject([k.dpush(pushes) for k in self.subs],pos=self,verdepth=self.verdepth+pushes.lenchange())

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is RefTree: other = other.unwrap()
		if type(other) is not SubsObject: return False
		if len(self.subs) != len(other.subs): return False
		return all(self.subs[k].compare(other.subs[k],odsc,thot,extract,lefpush,rigpush) for k in range(len(self.subs)))
	def phase1(self,indesc):
		def _dbgEnter():
			indesc.setSafety(0)
			self.setSafety(indesc.beginlen())
		return [(s.name,(s.obj,False)) if s.obj.needscarry() else (s.name,s.obj.verify(indesc,reqtype=True)) for s in self.subs]
	def phase1_gentle(self):
		def _dbgEnter():
			self.setVerified()
		for s in self.subs: assert s.name == None
		return [(None,(s.obj,True)) for s in self.subs]
	def needscarry(self):
		return True
		# return any(k.name!=None or k.obj.needscarry() for k in self.subs)
	
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		if carry==None:  raise TypeRequiredError(self,False)
		if type(carry) is not DualSubs:
			ocarry = carry.mangle_UE() if type(carry) is RefTree else None
			if type(ocarry) is not DualSubs: raise NonUnionTypeError(self,carry,indesc)
			carry = ocarry

		oflow = []
		garbo = carry.compacassign(self.phase1(indesc),overflow=oflow)
		if len(oflow): raise VariableAssignmentError(self,oflow[0][0])

		try:
			st = carry.peelcompactify(indesc,garbo,earlyabort=False)[0]
		except LanguageError as u:
			u.callingcontext([("(Constructing element of union)",carry,len(indesc),indesc,None)],0)
			raise u

		return SubsObject(st.extractbetween(carry),verdepth=len(indesc),pos=self)
class Template(Tobj):
	@initTobj
	def __init__(self,src,NSC=None,rows=None,subs=None,pos=None):
		# assert type(subs) is SubsObject
		self.NSC = ([],[]) if NSC==None else NSC
		self.rows = [] if rows == None else rows
		self.subs = [] if subs == None else subs
		self.src = src
		transferlines(self,pos)
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
		assertstatequal(indesc,self,carry,u_type(len(indesc)))
		src = self.src.verify(indesc,u_type(len(indesc)))
		osrc = src
		if type(src) is RefTree: src = src.mangle_UE()
		if type(src) is not DualSubs:
			raise LanguageError(self,"Can only apply templating to {"+"} object.")
		if len(self.NSC[0])!=len(self.NSC[1]):
			raise LanguageError(self,"Renaming statements must have an equal number of names on both sides.")
		for k in self.NSC[0]+self.NSC[1]:
			if type(k) is list: raise LanguageError(self,"You can't recursively nest renaming statements.")
		outp = src.applytemplate(indesc,self.NSC,self.subs,self.rows,self,shortname=osrc)
		if reqtype: return (outp,u_type(len(indesc)))

		# assert outp.src!=None
		return outp





	def prepr(self,context):
		add = []
		# if len(self.NSC[0])==0 and len(self.NSC[1])==0: add=[]
		# elif self.NSC[0]==self.NSC[1]: add = [pmultilinelist(self.NSC[0],context)]
		# else: add = [pmultilinelist(self.NSC[0],context)+"="+pmultilinelist(self.NSC[1],context)]
		return self.src.prepr(context)+"<"+",".join(add+[k.prepr(context) for k in self.rows]+[k.prepr(context) for k in self.subs])+">"
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		def calls(context_,out,prepend):
			pmultilinecsv(context,out,indent,self.rows+self.subs,prepend+"<",">"+postpend,callback=callback)
		self.src.pmultiline(context,out,indent,prepend,"",calls)
class Lambda(Tobj):
	@initTobj
	def __init__(self,si,obj,verdepth=None,pos=None):
		self.si = si
		# assert len(si)>0
		self.obj = obj
		self.verdepth = verdepth
		transferlines(self,pos)
		# if verdepth!=None:
		# 	self.verdepth = verdepth
		# 	self.complexity = 1+self.obj.complexity
		# 	self.touches = {k for k in self.obj.touches if k<verdepth}
		# 	self.softtouches = {k for k in self.obj.softtouches if k<verdepth}
	def writefile(self,file):
		file.writeChar("G")
		file.writeStrInc(self.si)
		self.obj.writefile(file)

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
	def detect(self,ranges):
		return self.obj.detect(ranges)

	def dpush(self,pushes,exob=None):
		if exob!=None:
			aftburn = self.verdepth+pushes.lenchange()
			jsi = self.si[:len(exob.subs)] if len(self.si)>len(exob.subs) else self.si
			nexob = SubsObject(exob.subs[:len(self.si)],verdepth=exob.verdepth) if len(exob.subs)>len(self.si) else exob
			adob = None
			if len(exob.subs)>len(self.si):
				adob = SubsObject(exob.subs[len(self.si):],verdepth=exob.verdepth).dpush(ScopeDelta([(aftburn-exob.verdepth,exob.verdepth)]))
			jobj = self.obj.dpush(pushes+ScopeDelta([(coflattenunravel(jsi,nexob,aftburn),),(-longcount(jsi),aftburn)]),exob=adob)
			if len(self.si)>len(exob.subs): jobj = jobj.addlambdasphase2(self.si[len(exob.subs):],pos=self)
			return jobj
		dis = self.obj.dpush(pushes).addlambdasphase2(self.si,pos=self)
		return dis



	def isemptyinst(self,si,prep=None):
		lc = striphuman(self.verdepth,self.si)[0]
		prep = lc if prep==None else prep+lc
		return self.obj.isemptyinst(si,prep=prep)

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is RefTree: other = other.unwrap()
		if (type(other) is not Lambda or len(self.si)!=len(other.si)) and type(self.obj) is RefTree and self.obj.core!=None:
			return self.obj.unwrap().addlambdasphase2(self.si).compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not Lambda: return False
		if len(self.si)<len(other.si) and conservativeeq(self.si,other.si[:len(self.si)]):
			return Lambda(self.si[len(self.si):],self.obj,verdepth=other.verdepth).compare(other,odsc,thot,extract,lefpush,rigpush)
		return conservativeeq(self.si,other.si) and self.obj.compare(other.obj,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		if len(self.si) == 0: return self.obj.needscarry()
		return True
	
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		if len(self.si) == 0: return self.obj.verify(indesc,carry,reqtype,then)
		if carry==None: raise TypeRequiredError(self,True)
		truncargs,ntype = carry.extractfibration(indesc,self.si,blame=self)
		flatver,converter = truncargs.flatten(ScopeDelta([]),self.si,then=True)
		nindesc = indesc.addflat(flatver)
		return self.obj.verify(nindesc,ntype.dpush(converter)).addlambdasphase2(self.si,pos=self)



	def prepr(self,context):
		if type(self.obj) is RefTree and self.obj.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.obj.name)):
			return self.obj.unwrapOne().addlambdasphase2(self.si).prepr(context)
		word = context.newcolors(self.si)
		return pmultilinelist(self.si,context,word)+self.obj.prepr(context.addbits(word))
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		if type(self.obj) is RefTree and self.obj.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.obj.name)):
			return self.obj.unwrapOne().addlambdasphase2(self.si).pmultiline(context,out,indent,prepend,postpend,callback=callback)
		word = context.newcolors(self.si)
		self.obj.pmultiline(context.addbits(word),out,indent,prepend+pmultilinelist(self.si,context,word),postpend,callback)
class Strategy(Tobj):
	@initTobj
	def __init__(self,args=None,type=None,verdepth=None,pos=None):
		global encounters
		self.args = DualSubs(pos=pos,verdepth=verdepth) if args == None else args
		self.type = type
		self.verdepth = verdepth
		transferlines(self,pos)
		# if verdepth!=None:
		# 	self.touches = set()
		# 	self.softtouches = set()
		# 	self.touches.update(self.args.touches)
		# 	self.softtouches.update(self.args.softtouches)
		# 	self.complexity = 1+self.args.complexity+self.type.complexity
		# 	if self.type!=None:
		# 		self.touches.update(self.type.touches)
		# 		self.softtouches.update(self.type.softtouches)
		# 	self.touches = {k for k in self.touches if k<verdepth}
		# 	self.softtouches = {k for k in self.softtouches if k<verdepth}
	def isemptytype(self):
		return self.type.isemptytype()



	def writefile(self,file):
		file.writeChar("E")
		self.args.writefile(file,shutup=True)
		self.type.writefile(file)

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

	def detect(self,ranges):
		ranges = ranges.isolate()
		return self.args.detect(ranges,merge=True) or self.type.detect(ranges)

	def dpush(self,pushes,exob=None):
		disgrace = ScopeDelta()
		newargs = self.args.dpush(pushes,disgrace=disgrace)
		newtype = self.type.dpush(disgrace+pushes)
		dis = newtype.addfibration(newargs,pos=self)
		return dis

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is RefTree:
			att = other.mangle_FE()
			if att!=None: return self.compare(att,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not Strategy: return False
		if len(other.args)<len(self.args) and type(other.type) is RefTree:
			att = other.type.mangle_FE()
			if att!=None: return self.compare(att.addfibration(other.args),odsc,thot,extract,lefpush,rigpush)
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
	def addfibration(self,args,pos=None,alts=None):
		return Strategy(args+self.args,self.type,pos=self,verdepth=self.verdepth-longcount(args))
	def fulavail(self):
		return self.type.fulavail()
	def semavail(self,mog):
		return self.type.semavail(mog)
	def emptyinst(self,limit,mog,prep=None):

		# emptyinst now requires knowledge of its depth...

		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)


		trimargs = self.args.trimallnonessential()


		sc = longcount(trimargs)
		if prep == None: prep = SubsObject(verdepth=limit)
		prep = prep.dpush(ScopeDelta([(limit+sc-prep.verdepth,prep.verdepth)])).subs if prep != None else []

		art = trimargs.emptyinst(limit)

		tat = self.type.emptyinst(limit+sc,mog,SubsObject(prep+art.subs,verdepth=limit+sc))


		return Lambda([k.name for k in trimargs.rows],tat,verdepth=limit)

	def trimallnonessential(self,si=None):

		disgrace = ScopeDelta()
		nargs = self.args.trimallnonessential(si,disgrace)
		ntype = self.type
		if not disgrace.isempty(): ntype = ntype.dpush(disgrace)
		return Strategy(nargs,ntype,verdepth=self.verdepth,pos=self)


	@lazyflatten
	def flatten(self,delta,mog,assistmog,prep=None,obj=None,fillout=None,then=False):
		if obj != None:
			obj = obj.dpush(ScopeDelta([]),exob=self.args.emptyinst(obj.verdepth-longcount(self.args)))

		arp = self.args.dpush(delta)


		
		if prep == None:
			njprep = arp
		else:
			lindsk = self.verdepth+delta.lenchange()
			calmdown = prep.dpush(ScopeDelta([(lindsk-longcount(prep)-prep.verdepth,prep.verdepth)]))
			njprep = DualSubs(calmdown.rows+arp.rows,verdepth=calmdown.verdepth)

		return self.type.flatten(delta,mog,assistmog,njprep,obj,fillout=fillout,then=then)
	def needscarry(self):
		if len(self.args) == 0: return self.type.needscarry()
		return False
	

	def reverse_mangle_FE(self):
		# component = self.unwrap() if type(self) is RefTree else self
		# if type(component) is not Strategy: return None
		component = self.trimallnonessential()
		if type(component.type) is not RefTree: return None
		comptype = component.type.unwrap()
		if type(comptype) is not RefTree or comptype.src!=None or comptype.name!=1: return None
		return RefTree(1,SubsObject([
			SubRow(None,comptype.args.subs[0].obj.addfibration(component.args)),
			SubRow(None,comptype.args.subs[1].obj.addlambdasphase2([j.name for j in component.args.rows])),
			SubRow(None,comptype.args.subs[2].obj.addlambdasphase2([j.name for j in component.args.rows]))
		],verdepth=self.verdepth),verdepth=self.verdepth)

	def verify(self,indesc,carry=None,reqtype=False,then=False):
		verargs,thendesc = self.args.verify(indesc,then=True)
		if len(verargs) == 0:
			# thendesc = thendesc.posterase(len(indesc))
			return self.type.verify(thendesc,carry.dpush(ScopeDelta([(longcount(verargs),len(indesc))])),reqtype=reqtype,then=then).dpush(ScopeDelta([(-longcount(verargs),len(indesc))]))

		assertstatequal(indesc,self,carry,u_type(len(indesc)))
		vertype = self.type.verify(thendesc,u_type(len(thendesc)))
		outp = vertype.addfibration(verargs)

		return (outp,u_type(len(indesc))) if reqtype else outp
	def prepr(self,context):
		if type(self.type) is RefTree and self.type.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.type.name)):
			return self.type.unwrapOne().addfibration(self.args).prepr(context)

		if context.littleeasier and any(row.obj!=None for row in self.args.rows) and self.verdepth!=None:
			return self.trimallnonessential().prepr(context)
		res = []
		for k in self.args.rows:
			word = context.newcolors(k.name)
			res.append(k.prepr(context,word=word))
			context = context.addbits(word)
		return context.red("[")+",".join(res)+context.red("]")+(self.type.prepr(context) if self.type!=None else "None")
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		if type(self.type) is RefTree and self.type.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.type.name)):
			return self.type.unwrapOne().addfibration(self.args).pmultiline(context,out,indent,prepend,postpend,callback=callback)

		if context.littleeasier and any(row.obj!=None for row in self.args.rows) and self.verdepth!=None:
			return self.trimallnonessential().pmultiline(context,out,indent,prepend,postpend,callback)
		def calls(context,out,prepend):
			self.type.pmultiline(context,out,indent,prepend,postpend,callback=callback)
		pmultilinecsv(context,out,indent,self.args.rows,prepend+context.red("["),context.red("]"),lamadapt=lambda x:x.name,callback=calls,delim=context.red(","))
def u_type(verdepth):
	return RefTree(verdepth=verdepth)
class RefTree(Tobj):
	@initTobj
	def __init__(self,name=None,args=None,src=None,safety=None,verdepth=None,pos=None,core=None):
		self.name       = 0 if name == None else name
		self.args       = SubsObject(verdepth=verdepth) if args == None else args
		self.src        = src
		self.core       = core
		self.safety     = safety
		self.verdepth   = verdepth

		transferlines(self,pos)
		def _dbgTest():
			if self.src==None and self.verdepth!=None and self.name!=0:
				assert self.name<self.verdepth
			assert type(self.args) is SubsObject
		# assert not isinstance()
		# assert type(self.name) is int or type(self.name) is str
		# if verdepth!=None:
		# 	self.touches = set()
		# 	self.softtouches = set()
		# 	self.verdepth = verdepth
		# 	self.complexity = 1+(self.src.complexity if self.src!=None else 0) + self.args.complexity
		# 	self.touches.update(self.args.touches)
		# 	self.softtouches.update(self.args.softtouches)
		# 	if self.src!=None: self.touches.update(self.src.touches)
		# 	if self.src!=None: self.softtouches.update(self.src.softtouches)
		# 	if type(self.name) is int and self.src==None:
		# 		assert self.name<verdepth or self.name==0
		# 		else: self.softtouches.add(self.name)

		# 	assert self.src==None or type(self.src) is RefTree or type(self.src.core) is RefTree
		# assert type(self.args) is SubsObject


	def writefile(self,file):
		if len(self.args.subs):
			if self.src==None:
				file.writeChar("H")
				file.writeNum(self.name)
				self.args.writefile(file,shutup=True)
			else:
				file.writeChar("I")
				file.writeNum(self.name)
				self.args.writefile(file,shutup=True)
				self.src.writefile(file)
		else:
			if self.src==None:
				file.writeChar("A")
				file.writeNum(self.name)
			else:
				file.writeChar("B")
				file.writeNum(self.name)
				self.src.writefile(file)


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

	def unwrap(self):
		if self.core==None: return self
		ja = self.unwrapOne()
		if type(ja) is RefTree: ja = ja.unwrap()
		return ja

	def unwrapOne(self):
		return self.core.core.dpush(self.core.rows,exob=self.args if len(self.args.subs) else None)

	def detect(self,ranges):
		if self.core!=None:
			# if not self.core.rows.canGlom():
			# 	return self.unwrap().detect(ranges)
			# 	# if self.core.core.dpush(self.core.rows).detect(ranges): return True
			# 	# 	return self.unwrap().detect(ranges)
			# else:

			if self.args.detect(ranges): return True
			if ranges.islowerbound(self.name): return False
			return self.core.core.detect(self.core.rows + ranges)#<><><> account for special case
			
		elif self.src==None:
			if not ranges.canTranslate(self.name): return True
		elif self.src.detect(ranges): return True
		return self.args.detect(ranges)
	def dpush(self,pushes,exob=None):
		gy = self.name

		pushdepth = self.verdepth+pushes.lenchange()
		if exob!=None and exob.verdepth<pushdepth: exob = exob.dpush(ScopeDelta([(pushdepth-exob.verdepth,exob.verdepth)]))
		# ogy = self.name

		# assert 

		if self.src!=None:
			decargs = self.args if pushes.isempty() else self.args.dpush(pushes)
			if exob != None: decargs = SubsObject(decargs.subs+exob.subs,verdepth=pushdepth)

			outp = self.src.dpush(pushes)
			agar = outp.isSubOb()
			if type(agar) is not bool or not agar:
				outp = RefTree(src=outp,args=decargs,name=self.name,verdepth=outp.verdepth,pos=self,core=None if self.core==None else self.core.dpush_ds(pushes))
			else:
				outp = outp.reference(self.name)
				if len(decargs.subs): return outp.dpush(ScopeDelta(),exob=decargs)
			return outp
		if self.name!=0:
			if self.core!=None and not pushes.canTranslate(self.name,ignoresubs=True):
				decargs = self.args if pushes.isempty() else self.args.dpush(pushes)
				if exob != None: decargs = SubsObject(decargs.subs+exob.subs,verdepth=pushdepth)

				return self.core.core.dpush(self.core.rows+pushes,decargs if len(decargs.subs) else None)

			# if not pushes.canTranslate(self.name,ignoresubs=True):
				
			gy = pushes.translate(self.name,ignoresubs=self.core!=None)



		if type(gy) is int:

			decargs = self.args if pushes.isempty() else self.args.dpush(pushes)
			if exob != None: decargs = SubsObject(decargs.subs+exob.subs,verdepth=pushdepth)

			return RefTree(gy,decargs,None,pos=self,verdepth=pushdepth,core=None if self.core==None else self.core.dpush_ds(pushes))

		elif len(gy)==3:
			# teleport
			# (j[2],ScopeDelta(self.pushes[:i]),ScopeDelta(self.pushes[i+1:]))

			pard = self.dpush(gy[1]+ScopeDelta([(gy[0][0].verdepth-self.verdepth,gy[0][0].verdepth)]))
			for j in range(len(gy[0])):
				if pard.compare(gy[0][j]):
					# print("MAIJFOAIJFOIEJFOKJLSKJFDLSJFK"*3)
					vdep = self.verdepth+pushes.lenchange()-gy[2].lenchange()
					ae = RefTree(vdep-len(gy[0])+j,verdepth=vdep)
					if exob!=None or not gy[2].isempty():
						ae = ae.dpush(gy[2],exob=exob)
					return ae
			raise DpushError

		else:

			decargs = self.args if pushes.isempty() else self.args.dpush(pushes)
			if exob != None: decargs = SubsObject(decargs.subs+exob.subs,verdepth=pushdepth)

			assert self.verdepth+gy[3]-gy[0].verdepth>=0
			# outp = gy[0].dpush(ScopeDelta([(self.verdepth+gy[3]-gy[0].verdepth,gy[0].verdepth)])+gy[1],exob=decargs if len(decargs.subs) else None)

			if not gy[1].canTranslate(gy[2]):
				outp = gy[0].dpush(ScopeDelta([(self.verdepth+gy[3]-gy[0].verdepth,gy[0].verdepth)])+gy[1],exob=decargs if len(decargs.subs) else None)
				return outp
			else:
				assert self.core == None
				cr = gy[1].translate(gy[2])
				return RefTree(
					cr,
					decargs,
					pos=self,
					verdepth=pushdepth,
					core = DelayedSub(gy[0],ScopeDelta([(self.verdepth+gy[3]-gy[0].verdepth,gy[0].verdepth)])+gy[1])
				)


	def isemptyinst(self,si,prep=None):
		if type(si) is list: return False
		if self.name!=si: return False
		return self.args.isemptyinst([] if prep==None else prep)

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if self.src != None:
			if type(other) is not RefTree: return False
			if other.src==None: other = other.unwrap()
			if other.src==None or self.name!=other.name: return False
			return self.src.compare(other.src,odsc,thot,extract,lefpush,rigpush) and self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush)
		pTest = self.isSubOb()
		if thot != None and type(pTest) is int:
			for k in thot:
				if k[0] == pTest:
					subself = self.unwrap()
					for j in extract:
						if j[0] == k[1] and j[2] == False:
							return True
					repls = []
					valid = True
					dsc = subself.verdepth+(0 if lefpush==None else lefpush.lenchange())
					for g1 in range(len(subself.args.subs)):
						if type(subself.args.subs[g1].obj) is not RefTree or subself.args.subs[g1].obj.name<odsc:
							valid = False
							break
						for g2 in range(g1):
							if subself.args.subs[g1].obj.compare(subself.args.subs[g2].obj):
								valid = False
								break
						if not valid: break
						repls.append(subself.args.subs[g1].obj)
					if not valid: break
					try:
						gr = other.dpush((ScopeDelta() if rigpush==None else rigpush) + (ScopeDelta([(odsc-dsc,odsc,repls)])) if len(repls) else ScopeDelta([(odsc-dsc,odsc)]))
					except DpushError:
						return False
					mod = gr.addlambdasphase2(["_"]*len(repls))
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(mod)
					extract.append((k[1],mod,True))
					return True
		if self.core==None and type(other) is RefTree and other.core!=None: other=other.unwrap()
		if self.core!=None and (type(other) is not RefTree or other.core==None): return self.unwrap().compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is Strategy: 
			att = self.mangle_FE()
			if att==None:
				natt = other.reverse_mangle_FE()
				if natt==None: return False
				return self.compare(natt,odsc,thot,extract,lefpush,rigpush)
			return att.compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is DualSubs:
			att = self.mangle_UE()
			if att==None: return False
			return att.compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not RefTree or other.src!=None: return False
		def incompare(a,b):
			if lefpush != None: a = lefpush.translate(a)
			if rigpush != None: b = rigpush.translate(b)
			return a == b
		if self.core==None and other.core==None:
			return incompare(self.name,other.name) and self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush)
		aH=self
		bH=other
		a = []
		b = []
		while True:
			if type(aH) is RefTree and aH.core!=None:
				for g in b:
					if incompare(aH.name,g.name): return aH.args.compare(g.args,odsc,thot,extract,lefpush,rigpush)#<><><> special case here... (arg order invariant or unused.)
				a.append(aH)
				aH = aH.unwrapOne()
			if type(bH) is RefTree and bH.core!=None:
				for g in a:
					if incompare(g.name,bH.name): return g.args.compare(bH.args,odsc,thot,extract,lefpush,rigpush)
				b.append(bH)
				bH = bH.unwrapOne()
			if (type(aH) is not RefTree or aH.core==None) and (type(bH) is not RefTree or bH.core==None):
				return aH.compare(bH,odsc,thot,extract,lefpush,rigpush)



	def needscarry(self):
		return False
	


	def verify(self,indesc,carry=None,reqtype=False,then=False):
		# print("VERIFY ENTER: ",type(self),self.name,self.src==None)
		assert not then
		# if type(self.name) is str and self.name.endswith(".ax'"):
		# 	assertstatequal(indesc,self,carry,u_type(len(indesc)))
		# 	search = self.name.replace("'","")
		# 	for i in range(len(indesc.oprows.dependencies)):
		# 		if indesc.oprows.dependencies[i][0]==search:
		# 			tue = RefTree(
		# 				name=-1-i,
		# 				core=DelayedSub(indesc.oprows.dependencies[i][1],ScopeDelta([(len(indesc),0)])),
		# 				verdepth=len(indesc)
		# 			)
		# 			break
		# 	else: assert False
		# 	return (tue,u_type(len(indesc))) if reqtype else tue

		p1 = self.args.phase1(indesc)
		errorcontext = []
		if self.src == None:
			# print("symextract ENTER: ",type(self),self.name)
			tra = indesc.symextract(self.name,p1,carry=carry,reqtype=reqtype,safety=self.safety,pos=self,errorcontext=errorcontext)
			# print("symextract EXIT: ",type(self),self.name)


			if tra != None: return tra
			for a in range(len(indesc.flat)):
				if indesc.flat[a].name==self.name and (-indesc.prepushes).canTranslate(a):
					raise LanguageError(self,"Symbol not defined for these arguments: "+self.name).callingcontext(errorcontext,-1)
			raise LanguageError(self,"Symbol not defined in this context: "+self.name).callingcontext(errorcontext,-1)
		else:
			if self.src.needscarry(): raise LanguageError(self,"Need to be able to generate type for property access...")
			orig = self.src.verify(indesc,reqtype=True)
			examtype = orig[1].mangle_UE() if type(orig[1]) is RefTree else orig[1]
			if examtype!=None and type(examtype) is DualSubs:

				anguish = examtype.flatten(ScopeDelta([]),obj=orig[0])
				tra = indesc.invisadd(anguish).preerase(len(anguish)).symextract(self.name,p1,carry=carry,reqtype=reqtype,safety=self.safety,limiter=len(indesc.flat),pos=self,errorcontext=errorcontext)
				if tra != None: return tra

			possib = orig[0]
			while type(possib) is RefTree:
				if possib.src == None:

					retrievalname = indesc.flat[(-indesc.postpushes).translate(possib.name)].name
					print("RETRIEVALNAME: ",retrievalname,self.name)

					tra = indesc.symextract(retrievalname+"."+self.name,possib.args.phase1_gentle()+p1,reqtype=reqtype,carry=carry,safety=self.safety+len(possib.args.subs) if self.safety!=None else None,pos=self,cosafety=len(possib.args.subs),errorcontext=errorcontext)
					if tra != None: return tra
				if possib.core==None: break
				possib = possib.unwrapOne()

			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,carry=carry,safety=self.safety+1 if self.safety!=None else None,pos=self,errorcontext=errorcontext)
			if tra != None: return tra
			raise LanguageError(self,"Symbol not defined for these arguments as a property access, macro, or operator overload: "+self.name).callingcontext(errorcontext,-1)
	def prepr(self,context):
		if self.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.name)):
			return self.unwrapOne().prepr(context)
		# if self.core!=None: return self.unwrap().prepr(context)
		res = str(context.getname(self.name)) if self.src==None else str(self.name)
		if self.src != None: res = self.src.prepr(context)+"."+res
		if len(self.args.subs)>0: res = res+"("+",".join([k.prepr(context) for k in self.args.subs])+")"
		return res
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		if self.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.name)):
			return self.unwrapOne().pmultiline(context,out,indent,prepend,postpend,callback=callback)
		# if self.core!=None: return self.unwrap().pmultiline(context,out,indent,prepend,postpend,callback=callback)
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
		component = self.unwrap()
		if type(component) is not RefTree: return component
		if component.name==1 and component.src==None:
			jab = component.args.subs[0].obj
			if type(jab) is RefTree: jab = jab.unwrap()
			if type(jab) is Strategy:
				reduc = jab.trimallnonessential()
				despar = ScopeDelta([(reduc.type.verdepth-self.verdepth,self.verdepth)])
				newparams = reduc.args.emptyinst(self.verdepth)
				return Strategy(reduc.args,RefTree(1,SubsObject([
					SubRow(None,reduc.type),
					SubRow(None,component.args.subs[1].obj.dpush(despar,exob = newparams)),
					SubRow(None,component.args.subs[2].obj.dpush(despar,exob = newparams))
				],verdepth=reduc.type.verdepth),verdepth=reduc.type.verdepth),verdepth=self.verdepth)
		if self.core!=None: return component
		# else:
		# 	print("CALL FAILED")
		# 	print(component.name)
		# 	print(component.src==None)
		# 	print(len(component.args.subs))
		return None




	def mangle_UE(self):
		delta = ScopeDelta([])
		component = self.unwrap()
		if type(component) is not RefTree: return component
		if component.name==1 and component.src==None:
			jab = component.args.subs[0].obj
			if type(jab) is RefTree: jab = jab.unwrap()
			if type(jab) is DualSubs:
				trimmed = jab.trimallnonessential()
				substuff = [(component.args.subs[1].obj.reference(s),component.args.subs[2].obj.reference(s)) for s in range(len(trimmed.rows))]
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
						if trimmed.rows[a].type.detect(ScopeDelta([(-tlc,lc)])): refs = sorted(refs+[k for k in sofrefs[b] if k not in refs])
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
								SubRow(None,trimmed.rows[a].type.dpush(delta+toalc)),
								SubRow(None,substuff[refs[0]][0].dpush(toalc)),
								SubRow(None,substuff[refs[0]][1].dpush(toalc))
							],verdepth=alc),verdepth=alc)
						))
					elif len(refs) == 2:
						outs.append(TypeRow(
							trimmed.rows[a].name,
							RefTree(1,SubsObject([
								SubRow(None,trimmed.rows[a].type.dpush(delta+toalc)),
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
								SubRow(None,trimmed.rows[a].type.dpush(delta+toalc)),
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
					delta = delta + ScopeDelta([(coflattenunravel(trimmed.rows[a].name,substuff[a][1],self.verdepth),),(-aalc,self.verdepth)])
				return DualSubs(outs,verdepth=self.verdepth)
		if self.core!=None: return component
		return None
class OperatorSet(Tobj):
	def primToJSON(self):
		return (
			"OperatorSet",#"type":
			[k.PJID if type(k) is not str else k for k in self.array]#"array":
		)
	@initTobj
	def __init__(self,array,pos=None):
		self.array = array
		transferlines(self,pos)
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
		outp = douparse(fulltree[0],carry=carry)
		return outp if reqtype else outp[0]
	def prepr(self,context):
		ssa = []
		for k in self.array:
			if type(k) is str: ssa.append(k)
			elif type(k) is OperatorSet: ssa.append(context.red("(")+k.prepr(context)+context.red(")"))
			else: ssa.append(k.prepr(context))
		return " ".join(ssa)
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
				rowprep = ""


@v_args(meta=True)
class MyTransformer(Transformer):
	def start(self,children,meta):
		deps = []
		rows = []
		for child in children[:-1]:
			if type(child) is tuple:
				rows.append(child)
			else:
				deps.append(child)
		return (deps,rows,children[-1])
	def precrow(self,children,meta):
		if type(children[-1]) is dict:
			return (children[:-1],children[-1])
		return (children,{'associate':'left'})
	def leftassoc(self,children,meta):
		return {'associate':'left'}
	def rightassoc(self,children,meta):
		return {'associate':'right'}

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
				# 	obj = Lambda(children[1].args.semavail(),obj,pos=meta)
			return TypeRow(children[0][0],children[1],obj,children[0][1])
		obj = None
		if len(children)>1:
			obj = children[1]
			# if type(children[0]) is Strategy:
			# 	obj = Lambda(children[0].args.semavail(),obj,pos=meta)
		return TypeRow(None,children[0],obj,{'silent':False,'contractible':False})
	def inferreddeclaration(self,children,meta):
		ty = None if len(children)<3 else Strategy(args=children[1],type=None,pos=meta)
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
		return RefTree(name,SubsObject(args,pos=meta),src,safety,pos=meta)
	def lamb(self,children,meta):
		coal = []
		for c in children[:-1]:
			coal+=c
		return Lambda(coal,children[-1],pos=meta)
	def template(self,children,meta):
		if   len(children)==1: return Template(children[0],pos=meta)
		elif len(children)==2: return Template(children[0],None,children[1][0],children[1][1],pos=meta)
		elif len(children)==3: return Template(children[0],(children[1],children[1]),children[2][0],children[2][1],pos=meta)
		elif len(children)==4: return Template(children[0],(children[1],children[2]),children[3][0],children[3][1],pos=meta)
		else: assert False
	def mixedsubs(self,children,meta):
		return ([c for c in children if type(c) is TypeRow],[c for c in children if type(c) is SubRow])

	def strategy(self,children,meta):
		args = []
		for j in children[:-1]:
			args += j.rows
		return Strategy(DualSubs(args,pos=meta),children[-1],pos=meta)
	def string(self,children,meta):
		return str(children[0]).replace("'","")
	def operators(self,children,meta):
		return OperatorSet(children,pos=meta)
	def subsobject(self,children,meta):

		return SubsObject(children,pos=meta)
	def wsubsobject(self,children,meta):
		if len(children):
			if len(children[0].subs) == 1 and children[0].subs[0].name==None:
				return children[0].subs[0].obj
			else:
				return children[0]
		else:
			return SubsObject(pos=meta)

	def dualsubs(self,children,meta):
		return DualSubs(children,pos=meta)
	def wdualsubs(self,children,meta):
		return children[0] if len(children) else DualSubs(pos=meta)
class Untransformer:
	def __init__(self,dict,head=0):
		self.dict = dict
		self.head = head
	def update(self,scope):
		for s in scope:
			if s.obj!=None: self.dict[self.head] = s.obj
			self.head+=1
		return self
	def isolate(self):
		return Untransformer(self.dict,self.head)
	def emptywrite(self,amt):
		return Untransformer(self.dict,self.head+amt)
	def getat(self,ind):
		if ind not in self.dict: return None
		ob = self.dict[ind]
		return DelayedSub(ob,ScopeDelta([(self.head-ob.verdepth,ob.verdepth)]))
	def objwrite(self,ty,ds,si):
		if ds==None:
			self.head += longcount(si)
			return
		# shead = self.head
		if type(si) is not list:
			self.dict[self.head] = ds
			self.head+=1
		else:
			sel = ty
			if type(sel) is RefTree: sel = sel.mangle_UE()
			if type(sel) is Strategy: sel = sel.type
			if type(sel) is RefTree: sel = sel.mangle_UE()
			if type(sel) is not DualSubs: assert False
			assert len(sel.rows)==len(si)
			k=0
			for s in range(len(si)):
				if sel.rows[s].obj==None:
					self.objwrite(sel.rows[s].type,ds.reference(k),si[s])
					k+=1
				else:
					self.objwrite(sel.rows[s].type,sel.rows[s].obj,si[s])

		# assert self.head == shead+longcount(si)
class DataBlockWriter:
	def __init__(self,filename):
		self.writer = io.BufferedWriter(io.FileIO(filename, 'w'))
	def writeChar(self,char):
		self.writer.write(char.encode())
	def writeStr(self,str):
		self.writer.write((str+"'").encode())
	def writeNum(self,num):
		self.writer.write((str(num)+"'").encode())
	def writeStrInc(self,inc):
		if type(inc) is list:
			self.writeChar("'")
			for j in inc: self.writeStrInc(j)
			self.writeChar('"')
		else:
			self.writeStr(inc)
	def writeNumInc(self,inc):
		if type(inc) is list:
			self.writeChar("'")
			for j in inc: self.writeNumInc(j)
			self.writeChar('"')
		else:
			self.writeNum(inc)
	def writeHeader(self,md5,deps,ob):
		self.writeStr(md5)
		self.writeNum(len(deps))
		for a,b in deps:
			self.writeStr(a)
			self.writeStr(b)
		for o in ob:
			o.writefile(self)
class DataBlockTransformer:
	def __init__(self,block,head):
		self.block = block
		self.head = head
	def readChar(self):
		self.head+=1
		return self.block[self.head-1]
	def readStr(self):
		oh=self.head
		while self.block[self.head]!="'":self.head+=1
		self.head+=1
		return self.block[oh:self.head-1]
	def readNum(self):
		return int(self.readStr())
	def readStrInc(self):
		g = self.readStr()
		if g!='': return g
		vo = []
		while True:
			if self.block[self.head]=='"':
				self.head+=1
				return vo
			vo.append(self.readStrInc())
	def readNumInc(self):
		g = self.readStr()
		if g!='': return int(g)
		vo = []
		while True:
			if self.block[self.head]=='"':
				self.head+=1
				return vo
			vo.append(self.readNumInc())
	def generic(self,depth):
		code = self.readChar()
		if   code == "A":#reftree,src==None
			name = self.readNum()
			return RefTree(
				name=name,
				core=depth.getat(name),
				verdepth=depth.head
			)
		elif code == "B":#reftree,src!=None
			name = self.readNum()
			return RefTree(
				name=name,
				src=self.generic(depth),
				verdepth=depth.head
			)
		elif code == "H":#reftree,src!=None
			name = self.readNum()
			return RefTree(
				name=name,
				args=self.SubsObject(depth),
				core=depth.getat(name),
				verdepth=depth.head
			)
		elif code == "I":#reftree,src!=None
			name = self.readNum()
			return RefTree(
				name=name,
				args=self.SubsObject(depth),
				src=self.generic(depth),
				verdepth=depth.head
			)
		elif code == "C": return self.DualSubs(depth)
		elif code == "D": return self.DualSubs(depth,origin=(self.generic(depth),self.readNumInc()))
		elif code == "E": return self.Strategy(depth)
		elif code == "F": return self.SubsObject(depth)
		elif code == "G": return self.Lambda(depth)
		else: assert False
	def TypeRow(self,depth):
		code = self.readChar()
		if   code=="a": return TypeRow(None,self.generic(depth),None,{"silent":False,"contractible":False})
		elif code=="b": return TypeRow(None,self.generic(depth),None,{"silent":True,"contractible":False})
		elif code=="c": return TypeRow(None,self.generic(depth),self.generic(depth))
		elif code=="d": return TypeRow(self.readStrInc(),self.generic(depth),None,{"silent":False,"contractible":False})
		elif code=="e": return TypeRow(self.readStrInc(),self.generic(depth),None,{"silent":True,"contractible":False})
		elif code=="f": return TypeRow(self.readStrInc(),self.generic(depth),self.generic(depth))
		print(code)
		print("---"*4)
		assert False
	def DualSubs(self,depth,then=False,origin=None):
		if not then: depth = depth.isolate()
		odh = depth.head
		lim = self.readNum()
		rows = []
		for row in range(lim):
			rows.append(self.TypeRow(depth))
			depth.objwrite(rows[-1].type,rows[-1].obj,rows[-1].name)
		return DualSubs(rows,origin=origin,verdepth=odh)
	def Strategy(self,depth):
		odh = depth.head
		depth = depth.isolate()
		args = self.DualSubs(depth,then=True)
		return Strategy(args,self.generic(depth),verdepth=odh)
	def SubsObject(self,depth):
		lim = self.readNum()
		return SubsObject([SubRow(None,self.generic(depth)) for k in range(lim)],verdepth=depth.head)
	def Lambda(self,depth):
		si = self.readStrInc()
		outp = Lambda(si,self.generic(depth.emptywrite(longcount(si))),verdepth=depth.head)
		return outp
	def readHeader(self):
		md5 = self.readStr()
		lim = self.readNum()
		ok = []
		for c in range(lim):
			ok.append((self.readStr(),self.readStr()))
		return (md5,ok)
	def readScope(self,depth):
		rows = []
		while self.head!=len(self.block):
			rows.append(self.TypeRow(depth))
			depth.objwrite(rows[-1].type,rows[-1].obj,rows[-1].name)
		return rows


class FileLoader:
	def __init__(self,overrides=None,l=None,basepath="",redoAll=False,verbose=False):
		self.lark = l
		if l == None:
			with open("core.lark", "r") as f:
				self.lark = Lark(f.read(),parser='lalr',propagate_positions=True)
		self.basepath = basepath
		self.redoAll = redoAll
		self.verbose = verbose
		self.overrides = overrides if overrides!=None else {}

		self.md5s = {}

		self.deps    = []
		self.lengths = []
		self.cumu    = []

	def load(self,filename,circular=None):
		circular = [] if circular == None else circular
		if filename in circular: raise LanguageError(None,"Cyclic import: "+filename)
		if filename in self.deps: return
		if filename in self.overrides.keys(): document = self.overrides[filename]
		else:
			if not os.path.exists(self.basepath+filename): raise LanguageError(None,"Could not import file: "+filename)
			with open(self.basepath+filename,"r",encoding='utf-8') as f: document = f.read()
		md5 = hashlib.md5(document.encode()).hexdigest()
		self.md5s[filename] = md5
		if not self.redoAll and os.path.exists(self.basepath+filename+".ver"):
			with open(self.basepath+filename+".ver","r") as f:
				dbt = DataBlockTransformer(f.read(),0)
				try:
					fmd5,fdeps = dbt.readHeader()
				except: pass
				else:
					if fmd5==md5:
						valid = True
						for dep,dmd5 in fdeps:
							self.load(dep,circular+[filename])
							if self.md5s[dep]!=dmd5:
								valid = False
								break
						if valid:
							if True:
							# try:
								ver = dbt.readScope(Untransformer({}).update(self.cumu))
							# except: pass
							# else:
								tub = []
								hs = 0
								fve = [a[0] for a in fdeps]
								for i in range(len(self.deps)):
									ms = hs
									for l in range(i,len(fve)):
										if fve[l]==self.deps[i]:
											if l==i: break
											tub.append((hs,i_of,ms,self.lengths[i]))
											swp=tub[l]
											tub[l]=tub[i]
											tub[i]=swp
											break
										for a in range(len(self.deps)):
											if self.deps[a]==fve[l]: l_of = self.lengths[a]
										if l==i: i_of = l_of
										ms+=l_of
									else:
										tub.append((hs,self.lengths[i]))
									hs += self.lengths[i]
								self.cumu += ver if len(tub)==0 else [a.dpush(ScopeDelta(tub)) for a in ver]
								self.lengths.append(len(ver))
								self.deps.append(filename)
								print("loaded: ",self.basepath+filename)
								return
		if os.path.exists(self.basepath+filename+".ver"): os.remove(self.basepath+filename+".ver")
		deps,rows,ob = MyTransformer().transform(self.lark.parse(document))
		for dep in deps:
			self.load(dep,circular+[filename])
		olen = len(self.cumu)
		pexclude = []
		hs=0
		for dep in range(len(self.deps)):
			if self.deps[dep] in deps: hs+=self.lengths[dep]
			else: pexclude.append((self.lengths[dep],hs))
		obj,ncumu = ob.verify(ScopeObject(self.cumu,prpush=ScopeDelta(pexclude),oprows=ContextYam(rows)),then=True)
		DataBlockWriter(self.basepath+filename+".ver").writeHeader(md5,[(a,self.md5s[a]) for a in self.deps],[j for j in ncumu.flat[olen:]])
		print("verified: ",self.basepath+filename)
		self.cumu = ncumu.flat
		self.lengths.append(len(self.cumu)-olen)
		self.deps.append(filename)






# try:
# 	compilefiles({"grouptheory.ax"},verbose=True)
# except LanguageError as u:
# 	u.tohtml()
# 	raise u


# compilefiles({"grouptheory.ax","builtin.ax"},redoAll=True,basepath="/Users/parkerlawrence/dev/agi/")
# compilefiles({"grouptheory.ax","builtin.ax"},redoAll=True,verbose=True,basepath="/Users/parkerlawrence/dev/agi/")

def _dbgTest():
	print("OSIDJFOIDJFS")
	# compilefiles({"grouptheory.ax","builtin.ax"},redoAll=True)
	# try:
	try:
	# 	# compilefiles({"grouptheory.ax","builtin.ax"},redoAll=True)
		# print("compiling")
		# compilefiles({"grouptheory.ax"},verbose=True,basepath="/Users/parkerlawrence/dev/agi/")
		FileLoader(verbose=True,basepath="/Users/parkerlawrence/dev/agi/",redoAll=False).load("grouptheory.ax")
	except LanguageError as u:
		u.tohtml()
		raise u
	# except LanguageError as u:
	# 	u.tohtml()
	# compilefiles({"builtin.ax"},redoAll=True)
	# print("debug")



#allow origin to be set to whatever object summoned it ---//> <><> that way you don't store dualsubs twice they tend to be bulky


#subsobject will need to redetect(tuple of src)                            on dpush...<>


#template can split things apart- need to allow this...<>


#really should crack down on (0,x) depth pushes.


#<>make it so a.b macros work a little more dilligently...


#if the time spent inside the compare function accounts for a significant portion of the runtime, then you should implement a list of previous substitutions to compare instead
#	those ladders may be subbed out already. they vanish when dpush clobbers them.


#you need to fine-tune the operator precidence and associativity.


#<><>make your code fast

#<>separate letter codes for no args

#<> re-establish coldvars...





