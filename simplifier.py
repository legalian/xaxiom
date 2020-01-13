
import copy
from inspect import getfullargspec
from .lark import Lark, UnexpectedInput, Transformer, v_args, InlineTransformer, Tree

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
					if isinstance(k,Tobj):
						lisrepr.append(k.prepr(context))
					else:
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
				if isinstance(lis[k],Tobj):
					lis[k].pmultiline(context,out,indent+1,"",delim if k<len(lis)-1 else "")
				else:
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
		if type(ahjs) is ScopeComplicator:
			assert ahjs.core.verdepth == amt+len(ahjs.secrets)
			for n in range(len(ahjs.secrets)):
				assert ahjs.secrets[n].verdepth == amt+n
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
		if type(ahjs) is ScopeComplicator:
			return ahjs.core.verdepth+len(ahjs.secrets)
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
# def _dbgEnter_detect(self,ranges):
# 	ranges.conforms(self.getSafety() if type(self) is not TypeRow and type(self) is not SubRow else self.getSafetyrow())
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
	pushes.objconforms(self,safe)
def _dbgExit_dpush(self,pushes,exob,outp):
	pamt = pushes.lenchange()
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
		outp.setSafetyrow(None if safe == None else safe+pamt)
	else:
		safe = self.getSafety()
		outp.setSafety(None if safe == None else safe+pamt)
		outp.setVerified()

	outp.alsubbedsafety = copy.copy(pushes.subprots(self.verdepth))
	if hasattr(self,'alsubbedsafety'):
		for k in self.alsubbedsafety:
			if pushes.canTranslate(k,inlen=safe):
				v = pushes.translate(k)
				if type(v) is not int:
					print(self.alsubbedsafety)
					print(pushes)
				assert type(v) is int
				assert v not in outp.alsubbedsafety
				outp.alsubbedsafety.append(v)


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
def _dbgEnter_flatten(self,delta,mog,assistmog,prep,obj,fillout,then):
	assert obj == None or isinstance(obj,Tobj)
	if prep != None:
		prep.setVerified()
	if obj != None:
		obj.setVerified()
		assert obj.verdepth<=self.verdepth+delta.lenchange()
		# obj.setSafety(self.getSafety())
	if prep!=None:
		assert prep.verdepth<=self.verdepth+delta.lenchange()#default to ==.
	self.setVerified()
	delta.objconforms(self,self.getSafety())

	# self.setSafety(indesc.beginlen())#tried to flatten something not slotted for beginninglen.
def _dbgExit_flatten(self,delta,mog,assistmog,prep,obj,fillout,then,ahjs):
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
	# if type(outp) is RefTree and outp.src==None and len(indesc.flat):
	# 	row = indesc.flat[(-indesc.postpushes).translate(outp.name)]
	# 	outp.debugname = row.name

	outp.alsubbedsafety = indesc.subprots()

def htmlformat(struct,context,prepend,postpend="",tabs=0,forbidrange=None):
	a = []
	struct.pmultiline(FormatterObject(context,forhtml=True,forbidrange=forbidrange),a,tabs,prepend,postpend)
	return "<br>".join([j.replace("&","&amp;").replace("\t","&nbsp;&nbsp;&nbsp;&nbsp;").replace("<","&lt;").replace(">","&gt;").replace("::lt::","<").replace("::gt::",">") for j in a])


class DpushError(Exception):
	pass

def htmlatlocation(basepath,filename,line,col,inner):
	res = "<div style='background-color:#789F2A;border-radius:5px;margin-bottom:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>Inside File "+filename+":</div><div style='background-color:#566C27;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
	res += "File: "+basepath+filename+"<br>"
	res += "Line: "+str(line)+"<br>"
	res += "Column: "+str(col)+"<br>"
	res += inner
	res += "</div></div>"
	return res


class LanguageError(Exception):
	def __init__(self,pos,message):
		Exception.__init__(self, message)
		# self.blame = 
		self.file = None
		self.pos = pos
		self.message = message
		transferlines(self,pos)
		self.soft = None
		self.choices = []
		self.callpattern = None
		self.argdata = None
	def setfile(self,file):
		self.file = file
		return self
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
		self.adfb=None
		# print("CONSTRUCTED WITH:",context)
	def innermessage(self):
		res =  htmlformat(self.expected,self.context,"Expected: ",forbidrange=self.hiddenrange())
		res += "<br>"
		res += htmlformat(self.got,self.context,"Provided: ",forbidrange=self.hiddenrange())
		if self.adfb!=None:
			if len(self.adfb)==1:
				res += "<br>Common inheritance ancestor found, but casting could not find an analagous component to this:"
				res += "<br>"
				res += htmlformat(self.adfb[0],self.context,"Expected side: ",forbidrange=self.hiddenrange())
			if len(self.adfb)==2:
				res += "<br>Common inheritance ancestor found, but implicit casting failed on this comparison: "
				res += "<br>"
				res += htmlformat(self.adfb[0],self.context,"Expected side: ",forbidrange=self.hiddenrange())
				res += "<br>"
				res += htmlformat(self.adfb[1],self.context,"Provided side: ",forbidrange=self.hiddenrange())
		return res

	def name(self):
		return "Type mismatch"
	def ihfb(self,ihfb):
		self.adfb=ihfb
		return self

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
		LanguageError.__init__(self,pos,"Too many positional arguments" if name==None else "Unexpected keyword argument: " + str(name))
	def name(self):
		return "Unexpected argument"
class DelayedSub:
	def __init__(self,core,rows=None):
		self.core = core
		self.rows = ScopeDelta() if rows==None else rows
		if any(len(j)==3 for j in self.rows.pushes):#9%
			self.core = self.core.dpush(self.rows)
			self.rows = ScopeDelta()
		self.isSubOb = self.core.isSubOb()
		def _dbgTest():
			self.rows.objconforms(self.core,self.core.verdepth)
			# assert not self.core.detect(self.rows)

		dok = self.rows
		while type(self.isSubOb) is int and not dok.isempty():
			try:
				self.isSubOb = dok.translate(self.isSubOb)
			except DpushError:
				self.isSubOb = None
				break
			if type(self.isSubOb) is tuple:
				dok = self.isSubOb[1]
				self.isSubOb = self.isSubOb[0].isSubOb()
			else: break

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
	def objconforms(self,obj,safe):
		obj.setSafety(safe)
		self.conforms(safe)
		if hasattr(obj,'alsubbedsafety'):
			car = self.subprots(safe)
			for j in obj.alsubbedsafety:
				if self.canTranslate(j,inlen=safe):
					jah = self.translate(j)
					assert type(jah) is int
					assert jah not in car
					car.append(jah)
	def conforms(self,safe):
		for i in range(len(self.pushes)):
			j = self.pushes[i]
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
					assert key<safe
					if symbol.verdepth>key:
						assert symbol.verdepth<=key
					trans = ScopeDelta([(safe-symbol.verdepth,symbol.verdepth)]+self.pushes[i+1:])
					if trans.canTranslate(key,inlen=safe):
						assert type(trans.translate(key)) is int

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

	# def breakdown(self):



	def subprots(self,fug):
		hama = []
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==2: fug += j[0]
			elif len(j)==3: fug += j[0]+len(j[2])
			elif len(j)==1:
				for key,symbol in j[0]:
					trans = ScopeDelta(self.pushes[i+1:])
					if trans.canTranslate(key): hama.append(trans.translate(key))
		for a in range(len(hama)):
			for b in range(a):
				assert hama[a]!=hama[b]
		return hama
	def canTranslate(self,fug,inlen=None,ignoresubs=False):
		changefar = 0
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==2:
				changefar += j[0]
				if fug>=j[1]:
					fug+=j[0]
					if fug<j[1]: return False
			elif len(j)==4:
				if   fug>=j[0] and fug<j[0]+j[1]: fug+=j[2]-j[0]
				elif fug>=j[2] and fug<j[2]+j[3]: fug+=j[0]-j[2]
				elif fug>=j[0]+j[1] and fug<j[2]: fug+=j[3]-j[1]
			elif len(j)==3:
				changefar += j[0]+len(j[2])
				if fug>=j[1]:
					if fug+j[0]<j[1]: return False
					fug+=j[0]+len(j[2])
			elif not ignoresubs:
				for key,symbol in j[0]:
					if fug==key:
						trans = ScopeDelta([(inlen+changefar-symbol.verdepth,symbol.verdepth)]+self.pushes[i+1:])
						return trans.islowerbound(key) or not symbol.detect(trans)
						# return symbol.detect(trans)
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
				changefar += j[0]+len(j[2])
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
	def __init__(self,context,magic=60,forhtml=False,forbidrange=None,littleeasier=True,colormap=None,fullrepresent=False,printcomplicators=False):
		self.magic = magic
		self.context = context.flatnamespace() if type(context) is ScopeObject else context
		self.forhtml = forhtml
		self.forbiddenrange = (forbidrange if forbidrange!=None else ScopeDelta()) - (context.prepushes+context.postpushes if type(context) is ScopeObject else ScopeDelta([]))#[] if forbidrange==None else forbidrange
		self.littleeasier = littleeasier
		self.colormap = {} if colormap==None else colormap
		self.fullrepresent = fullrepresent
		self.printcomplicators = printcomplicators

	def getname(self,name):
		if type(name) is str:
			if self.forhtml: return "::lt::span style='color:#fdee73'::gt::"+name+"::lt::/span::gt::"
			return name
		if self.context == None: return str(name)
		if type(name) is int:
			if name in self.colormap and self.forhtml:
				return "::lt::span style='color:"+self.colormap[name]+"'::gt::"+("{no name}" if self.context[name]==None else self.context[name])+"::lt::/span::gt::"
			if len(self.context)==0: return "{uni"+"verse}"
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
			printcomplicators=self.printcomplicators
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
	return plat[si]
def inR(si,val):
	if type(si) is list: return any(inR(s,val) for s in si)
	return val==si

def extfind(h,si,lc=0):
	if type(si) is list:
		for k in si:
			u,lc = extfind(h,k,lc)
			if u!=None: return (u,None)
		return (None,lc)
	if si==h: return (lc,None)
	return (None,lc+1)





def implicitcast(indesc,expected,provided,obj,blame=None,soften=False,extract=None,thot=None,odsc=None,owner=None):
	def _dbgEnter():
		assert expected==None or isinstance(expected,Tobj)
		assert isinstance(provided,Tobj)
		if expected!=None: expected.setSafety(obj.getSafety())
		provided.setSafety(obj.getSafety())

	if expected==None: return obj


	if type(provided) is ScopeComplicator: provided = provided.decode()
	if type(expected) is ScopeComplicator: expected = expected.decode()

	ihfb = None

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
					if type(provided) is RefTree: provided=provided.mangle_UE()
					pp,obk = provided.origin
					if type(pp) is ScopeComplicator: pp = pp.decode()
					if type(pp) is RefTree: pp = pp.mangle_UE()
					for p in range(1,pA):
						pp,obi = pp.origin
						if type(pp) is ScopeComplicator: pp = pp.decode()
						if type(pp) is RefTree: pp = pp.mangle_UE()
						obk = compose(obi,obk)
						# pp=opp

					print("GOING IN ",obk,[obk[i] for i in range(len(obk)) if pp.rows[i].obj==None])
					# provob = buildfrom([obk[i] for i in range(len(obk)) if pp.rows[i].obj==None],provided.flatten(ScopeDelta([]),[None]*len(provided.rows),obj=provob),provob.verdepth)
					provob = provided.inheritpopulate([obk[i] for i in range(len(obk)) if pp.rows[i].obj==None],provob)
					print("GOING OUT")

				if eA==0: return provob
				if type(expected) is RefTree: expected=expected.mangle_UE()
				pp,obk = expected.origin
				if type(pp) is ScopeComplicator: pp = pp.decode()
				if type(pp) is RefTree: pp = pp.mangle_UE()
				for e in range(1,eA):
					pp,obi = pp.origin
					if type(pp) is ScopeComplicator: pp = pp.decode()
					if type(pp) is RefTree: pp = pp.mangle_UE()
					obk = compose(obi,obk)
					# pp=opp

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
						if ihfb==None: ihfb = (expected.rows[h],)
						break

					vv = longcount(expected.rows[h].name)

					inquestion = guflat.flat[fou].obj.dpush(ScopeDelta([(-fou,provob.verdepth)]))
					if expected.rows[h].obj==None:
						finob.append(SubRow(None,inquestion))
						moat = moat + ScopeDelta([(longflattenunravel(expected.rows[h].name,expected.rows[h].type,inquestion,provob.verdepth)[0],),(-vv,provob.verdepth)])
					else:
						against = expected.rows[h].obj.dpush(moat)
						if not against.compare(inquestion,odsc,thot,extract):#<><><> make sure you aren't comparing things where they're set on both sides- that would be unesscesary.
							valid = False
							if ihfb==None: ihfb = (against,inquestion)
							break
						# moat = moat + ScopeDelta([(longflattenunravel(expected.rows[h].name,expected.rows[h].type,expected.rows[h].obj,provob.verdepth)[0],),(-vv,provob.verdepth)])
						moat = moat + ScopeDelta([(-vv,provob.verdepth)])
					# moat = moat + ScopeDelta([(longflattenunravel(expected.rows[h].name,expected.rows[h].type,inquestion,provob.verdepth)[0],),(-vv,provob.verdepth)])


				if valid: return SubsObject(finob,verdepth=provob.verdepth)
			if extract!=None:
				while st<len(extract): del extract[st]

			if type(headP) is ScopeComplicator: headP = headP.decode()
			if type(headE) is ScopeComplicator: headE = headE.decode()
			if type(headP) is RefTree: headP = headP.mangle_UE()
			if type(headE) is RefTree: headE = headE.mangle_UE()
			if type(headP) is Strategy:
				if type(headE) is Strategy and headE.args.compare(headP.args,odsc,thot,extract):
					assert False#now I have to worry about pushing with exob and then adding the SI back in... <><><>
					# return implicitcast(indesc,expected,provided,obj,blame=None,soften=False,extract=None,thot=None,odsc=None,owner=None)
				if extract!=None:
					while st<len(extract): del extract[st]
				raise TypeMismatch(blame,expected,provided,indesc).ihfb(ihfb).soften(soften)
			print(pA,eA)
			headP = headP.origin[0] if type(headP) is DualSubs and type(headE) is DualSubs and headP.origin!=None else None
			pA += 1
		headE = headE.origin[0] if type(headE) is DualSubs and type(headE) is DualSubs and headE.origin!=None else None
		eA += 1
	raise TypeMismatch(blame,expected,provided,indesc).ihfb(ihfb).soften(soften)





# found common ancestor?(first common ancestor) (second common ancestor does not have interesting properties.)
# 	add property to TypeMismatch that just prints underneath...
# 	expected inherits from ---> (one side)
# 	provided inherits from ---> (other side)

# 	print failed comparison...





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
			# if safe==0 and self.oprows!=None:
			# 	if type(self.flat[i]) is TypeRow and type(self.flat[i].obj) is RefTree and self.flat[i].obj.src==None:
			# 		cr1=(-self.postpushes).translate(self.flat[i].obj.name)
			# 		assert (self.flat[i].obj.core==None) == (self.flat[cr1].obj==None)



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
		databus = [k.name for k in self.flat]
		for amt,lim in self.postpushes.pushes:
			databus = databus[:lim]+databus[lim-amt:]
		return databus
	def subprots(self):
		hama = []
		for k in range(len(self.flat)):
			if self.flat[k].obj!=None and self.postpushes.canTranslate(k):
				hama.append(self.postpushes.translate(k))
		for a in range(len(hama)):
			for b in range(a):
				assert hama[a]!=hama[b]
		return hama



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


	def symextract(self,name,subs,carry=None,reqtype=False,limiter=None,pos=None,cosafety=None,errorcontext=None):
		def _dbgEnter():
			assert carry==None or isinstance(carry,Tobj)
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
					outp,ty = ahjs
					assert isinstance(outp,Tobj)
					assert isinstance(ty,Tobj)
					# if reqtype:
					ty.setSafety(len(self))
					# if pos!=None: assert outp.row!=0 or outp.column!=0
					outp.setVerified()
					outp.setSafety(len(self))

			if row == 0:
				return (u_type(len(self)),u_type(len(self)))
			cr=self.postpushes.translateGentle(row)
			curr = self.flat[row].type.dpush(ScopeDelta([(len(self)-cr,min(cr,len(self)))]))
			bedoin,cuarg,ntype = curr.extractfibrationSubs(self,subs,minsafety=cosafety,maxsafety=None if self.flat[row].silent==None else self.flat[row].silent['contractible'],blame=pos)

			ntype = complicate(ntype,cuarg.rip())
			# ntype = ntype.dpush(ScopeDelta([(-longcount(cuarg),len(self))]))


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

			errorcontext.insert(0,(name,self.flat[row].type,self.postpushes.translateGentle(row),self,None))
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
	def __init__(self,name,ty,obj=None,silent=None):
		self.name = name
		self.type = ty
		self.obj  = obj
		self.silent = silent
		if type(ty) is Lambda or type(ty) is SubsObject: assert False
		# assert self.type != None or self.obj != None
		assert type(self.type) is not Strategy or self.type.type != None or self.obj != None
		def _dbgTest():
			assert self.type==None or isinstance(self.type,Tobj)
			assert self.obj == None or isinstance(self.obj,Tobj)

	def writefile(self,file):
		file.writeChar(["a","b","c","d","e","f","g","h","i","j"][(0 if self.obj!=None else 1 if self.silent==None else 1+int(self.silent['silent'])*2+int(self.silent['contractible']!=None))*2+int(self.name==None)])
		if self.name!=None: file.writeStrInc(self.name)
		self.type.writefile(file)
		if self.obj!=None: self.obj.writefile(file)
		elif self.silent!=None and self.silent['contractible']!=None: file.writeNum(self.silent['contractible'])

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
		if self.silent!=None and self.silent['silent']:
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
		if self.silent!=None and self.silent['silent']:
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

	def __init__(self,name,obj):
		self.name = name
		self.obj  = obj
		def _dbgTest():
			assert isinstance(self.obj,Tobj)
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

	def decode(self):
		return self
	def getbecsafety(self):
		return None
	def isemptytype(self):
		return False
	def fulavail(self):
		raise InvalidSplit()
	def setVerified(self):
		assert self.verdepth!=None
		pass
	def setSafety(self,safe):
		if safe == None: return
		if hasattr(self,'foclnsafety'):
			if self.foclnsafety != safe:
				print(type(self))
				assert False
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
			if type(self) is ScopeComplicator:
				return self.decode().flatten(delta,mog,assistmog,prep,obj,fillout,then)
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
		if len(args) == 0:
			return complicate(self,args.rip(),pos=self)
			# return self.dpush(ScopeDelta([(-shaz,self.verdepth-shaz)]))
		return Strategy(args,self,verdepth=self.verdepth-longcount(args),pos=self if pos==None else pos)
	def addlambdas(self,args,pos=None):
		starter = self.verdepth-longcount(args)
		si = args.semavail()
		disgrace = ScopeDelta()
		largs = args.trimallnonessential(si,disgrace=disgrace)
		return (self.dpush(disgrace) if not disgrace.isempty() else self).addlambdasphase2(si,pos=pos)
	def addlambdasphase2(self,si,pos=None):
		def _dbgExit(outp):
			outp.setSafety(self.verdepth - longcount(si))
			assert outp.verdepth == self.verdepth - longcount(si)
		if len(si)==0: return self
		if type(self) is Lambda:
			return Lambda(si+self.si,self.obj,verdepth=self.verdepth,pos=self if pos==None else pos)
		elim=0
		fafter = self.verdepth#+len(self.secrets) if type(self) is ScopeComplicator else self.verdepth
		ndepth = self.verdepth
		starter = fafter-longcount(si)
		outp = self.core if type(self) is ScopeComplicator else self
		if type(outp) is RefTree and outp.name<starter:
			elim=0
			while elim<len(si) and elim<len(outp.args.subs):
				ndepth = starter+longcount(si[:len(si)-elim-1])
				if not outp.args.subs[len(outp.args.subs)-1-elim].obj.isemptyinst(striphuman(ndepth,si[len(si)-1-elim])[0]): break
				thisdepth = longcount(si[len(si)-elim-1])
				valid = True
				if outp.src!=None:
					if outp.src.detect(ScopeDelta([(-thisdepth,ndepth)])): 
						valid = False
				for k in outp.args.subs[:len(outp.args.subs)-1-elim]:
					if k.obj.detect(ScopeDelta([(-thisdepth,ndepth)])):
						valid = False
						break
				if not valid: break
				elim+=1
			if elim:
				ndepth = starter+longcount(si[:len(si)-elim])
				stretch = ScopeDelta([(ndepth-fafter,ndepth)])
				nsubs = SubsObject([k.dpush(stretch) for k in outp.args.subs[:len(outp.args.subs)-elim]],verdepth=ndepth)
				core = None
				if outp.core != None:
					core = outp.core.dpush_ds(stretch)
				outp = RefTree(outp.name,nsubs,None if outp.src==None else outp.src.dpush(stretch),verdepth=ndepth,pos=outp,core=core)
		if type(self) is ScopeComplicator:
			if elim==0:
				outp = self
			else:
				res,sof = semi_complicate_dpush(self.verdepth+ndepth-fafter,self.secrets,ScopeDelta([(ndepth-fafter,ndepth)]))
				outp = complicate(outp.dpush(sof),res)

				# outp = semi_complicate_dpush(outp.dpush(sof),res,ScopeDelta([(ndepth-fafter,ndepth)]),True)
		if len(si)==elim: return outp
		return correctLambda(si[:len(si)-elim],outp,ScopeDelta(),verdepth=starter,pos=self if pos==None else pos)





	def extractfibration(self,indesc,si,blame=None):
		if len(si)==0: return (DualSubs(verdepth=self.verdepth),self)
		try:
			carry = self.trimallnonessential(si) if type(self) is Strategy else self
		except InvalidSplit as u:
			u.reblame(blame,self.args,si,indesc)
			raise u
		ac = []
		while len(si)>len(ac):
			carry = carry.decode()
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
				carry = carry.decode()
				if type(carry) is RefTree:
					mogo = carry.mangle_FE()
					if mogo!=None: carry = mogo
				if type(carry) is not Strategy: break
				goneonce=True
				# preserve alts on mangle?

				oflow = []
				asgo = asgo + carry.args.rows
				midflow = DualSubs(asgo,verdepth=advdepth).compacassign(inflow,oflow,minsafety)
				# inflow = oflow
				carry = carry.type
				if not len(oflow): break


			if not goneonce: raise VariableAssignmentError(blame,inflow[0][0])
			(dbdbdb,earlyabort),(nindesc,ndelta) = DualSubs(asgo,verdepth=advdepth).peelcompactify(nindesc,midflow,then=True,earlyabort=earlyabort)
			if any(k.obj==None for k in dc): raise LanguageError(blame,"Hole in arguments list")

			if minsafety!=None: minsafety -= len(asgo)
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

		if maxsafety!=None and lensi!=0 and lensi<maxsafety: raise LanguageError(blame,"Not enough parameters").soften(True)

		advdepth = self.verdepth+longcount([a.name for a in ac[:lensi]])
		if lensi<len(ac):
			carry = carry.addfibration(DualSubs(dc[lensi:],verdepth=advdepth))
			ac = ac[:lensi]
			dc = dc[:lensi]
		return (DualSubs(ac,verdepth=self.verdepth),DualSubs(dc,verdepth=self.verdepth),carry)


	def rip(self):
		cu = []
		for row in range(len(self.rows)):
			if type(self.rows[row].name) is list:
				ho = self.rows[row].obj.widereference(self.rows[row].name)
				cu = cu+[ho[0]]+[ho[d].dpush(ScopeDelta([(d,self.verdepth+row)])) for d in range(1,len(ho))]
			else:
				cu.append(self.rows[row].obj)
		return cu


	def widereference(self,si):
		if type(si) is not list: return [self]
		cu = []
		for s in range(len(si)): cu = cu+self.reference(s).widereference(si[s])
		return cu
	def deepreference(self,su):
		k = self
		for s in su: k = k.reference(s)
		return k
	def reference(self,s):
		if type(self) is SubsObject: return self.subs[s].obj
		elif type(self) is ScopeComplicator:
			return ScopeComplicator(self.core.reference(s),self.secrets,verdepth=self.verdepth)
		elif type(self) is Lambda: return Lambda(self.si,self.obj.reference(s),verdepth=self.verdepth,pos=self)
		elif type(self) is RefTree and self.core!=None and type(self.isSubOb()) is bool and self.isSubOb():
			return self.unwrap().reference(s)
		return RefTree(src=self,name=s,verdepth=self.verdepth,pos=self)



	def __repr__(self):
		return self.prepr(FormatterObject(None))




	def isSubOb(self):
		if type(self) is ScopeComplicator:
			k = self.core.isSubOb()
			if type(k) is int:
				if k<self.verdepth: return k
				else: return self.secrets[k-self.verdepth].isSubOb()
			else: return k
		if type(self) is SubsObject: return True
		if type(self) is Lambda:
			k = self.obj.isSubOb()
			if type(k) is bool: return k
			if type(k) is int:
				if k<self.verdepth: return k
				else:
					def und(mog,k):
						if type(mog) is not list:
							if k==0: return []
							return k-1
						else:
							for m in range(len(mog)):
								u = und(mog[m],k)
								if type(u) is list: return [m]+u
								else: k = u
							return k
					return und(self.si,k)
			return [k[0]+len(self.si)]+k[1:]
		if type(self) is RefTree and self.core!=None:
			k = self.core.isSubOb
			if type(k) is list:
				if k[0]<len(self.args.subs):
					return self.args.subs.deepreference(k)
				else:
					return [k[0]-len(self.args.subs)]+k[1:]
			return k
		if type(self) is RefTree:
			if self.src==None: return self.name
			else:
				k = self.src.isSubOb()
				if type(k) is list:
					return k+[self.name]
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
	def _dbgTest():
		assert ob.verdepth!=None
	if type(si) is list:
		res = []
		for n in range(len(si)):
			res = res + coflattenunravel(si[n],ob.reference(n),left+len(res))
		return res
	return [(left,ob)]
def longflattenunravel(si,ty,ob,left):
	if type(si) is list:
		ty = ty.decode()
		ty = ty.type if type(ty) is Strategy else ty
		ty = ty.mangle_UE() if type(ty) is RefTree else ty
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

		sel2 = self.decode()
		sel1 = sel2.mangle_UE() if type(sel2) is RefTree else sel2
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
	def assertcomp(self,other):
		assert type(other) is DualSubs
		assert len(self.rows) == len(other.rows)
		for j in range(len(self.rows)):
			assert (self.rows[j].obj==None)==(other.rows[j].obj==None)
			self.rows[j].type.assertcomp(other.rows[j].type)
			if self.rows[j].obj!=None: self.rows[j].obj.assertcomp(other.rows[j].obj)

	@initTobj
	def __init__(self,rows=None,verdepth=None,origin=None,pos=None):
		self.rows = rows if rows != None else []
		self.origin = origin
		self.verdepth = verdepth
		transferlines(self,pos)
		def _dbgTest():
			for k in self.rows:
				assert type(k) is TypeRow
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

	def extractbetween(self,older,blame=None):
		for j in self.rows:
			if j.obj==None:
				raise LanguageError(blame,"Incomplete specification of function call.")
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

	def prepr(self,context):
		if context.littleeasier and any(row.obj!=None for row in self.rows) and self.verdepth!=None:
			return self.trimallnonessential().prepr(context)
		yud = []
		for k in self.rows:
			word = context.newcolors(k.name)
			yud.append(k.prepr(context,word=word))
			context = context.addbits(word)
		return context.red("{")+",".join(yud)+context.red("}")
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		if context.littleeasier and any(row.obj!=None for row in self.rows) and self.verdepth!=None:
			return self.trimallnonessential().pmultiline(context,out,indent,prepend,postpend,callback)
		pmultilinecsv(context,out,indent,self.rows,prepend+context.red("{"),context.red("}")+postpend,lamadapt=lambda x:x.name,callback=callback,delim=context.red(","))

	def detect(self,ranges):
		return any(row.obj==None and row.detect(ranges) for row in self.rows)

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
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else rigpush+other.correction())
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
					myu = m.type.decode()
					if type(myu) is RefTree: myu = myu.mangle_UE()
					if type(myu) is DualSubs:
						left = unshift(left,myu.rows,self.rows[k].name,si[s])
						kaname = copy.copy(m.name)
						restype = myu.trimallnonessential(si[s],alsokill=kaname)
						m = TypeRow(kaname,restype,m.obj,m.silent)
					elif type(myu) is not Strategy: raise InvalidSplit()
					else:
						mot = myu.type.decode()
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
				if self.rows[n].obj == None and nobj!=None:
					jaaj = longflattenunravel(self.rows[n].name,self.rows[n].type,nobj,left)
					delta = delta + ScopeDelta([(jaaj[0],)])
				elif fillout!=left:
					delta = delta + ScopeDelta([(fillout,0,left,vv)])
				left += vv
			else:
				delta = delta + ScopeDelta([(len(nflat.flat),fillout)])
				left += len(nflat.flat)
				if self.rows[n].obj == None:
					if nobj == None:
						dbgdbg = left
						passprep = prep.emptyinst(dbgdbg,striphuman(dbgdbg-longcount(prep),prep.fulavail())[0]) if prep != None else None
						nobj = self.rows[n].type.emptyinst(dbgdbg,assistmog[n],prep=passprep)
					jaaj = longflattenunravel(self.rows[n].name,self.rows[n].type,nobj,left)
					delta = delta + ScopeDelta([(jaaj[0],)])
				delta = delta + ScopeDelta([(-vv,left)])
			fillout = fillout + len(nflat.flat)
		return (cu,delta) if then else cu





	def inheritpopulate(self,mapping,obj):
		def isimportant(m,start,run):
			if type(m) is not list: return m>=start and m<start+run
			return any(isimportant(a,start,run) for a in m)
		s = 0
		cu = []
		delta = ScopeDelta()
		left = 0
		for n in range(len(self.rows)):
			vv = longcount(self.rows[n].name)
			if self.rows[n].obj == None:
				nobj = obj.reference(s)
				s+=1
				jaaj = longflattenunravel(self.rows[n].name,self.rows[n].type,nobj,self.verdepth)
				delta = delta + ScopeDelta([(jaaj[0],)])
			else:
				nobj = self.rows[n].obj.dpush(delta) if isimportant(mapping,left,vv) else None
			if nobj==None:
				cu = cu+[None]*vv
			else:
				cu = cu+nobj.widereference(self.rows[n].name)			
			delta = delta + ScopeDelta([(-longcount(self.rows[n].name),self.verdepth)])
			left+=vv
		return buildfrom(mapping,cu,self.verdepth)








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
					obj = correctLambda(gnoa.semavail(),obj,despar,verdepth=len(indesc),pos=obj)
			else:
				nty = self.rows[n].type.verify(indesc,u_type(len(indesc)))
				obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None


			try:
				if self.rows[n].name == "*****":
					uwa = nty.decode()
					if type(uwa) is RefTree:
						uwa = uwa.mangle_UE()
						if uwa==None: raise InvalidSplit()
						self.rows[n].name = uwa.fulavail()
					else: self.rows[n].name = uwa.fulavail()

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
		return self.compacrecurse(compyoks,[],[],indesc,ScopeDelta([]),then=then,earlyabort=earlyabort)

	def compacassign(self,inyoks,overflow=None,cosafety=None):
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
				# if safety != None and s < safety:
				# 	raise VariableAssignmentError(inyoks[s][1][0],inyoks[s][0])
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
		def restart():
			if len(trail)==0:
				return self.compacrecurse(yoks,trail,prep,startindesc,startdelta,then=then,earlyabort=earlyabort)
			return (len(trail)-1,earlyabort)

		def namerical(lim,names,sof):
			if type(names) is not list: return [(lim,sof)]
			i = []
			for j in range(len(names)):
				i = i+namerical(lim+len(i),names[j],sof+[j])
			return i
		thot = prep
		for n in range(len(self.rows)):
			row = self.rows[n]
			
			# try:
			rowtype = row.type.dpush(delta)
			# except AssertionError:
			# 	print([a.name for a in self.rows])
			# 	assert False
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
									if ming!=None: return restart()
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

										yfactor = indesc.addflat(truncargs.flatten(ScopeDelta(),yoks[k][1].si))
										# print("ENTER ",yfactor)
										# yasat = truncargs.dpush(ScopeDelta([(-lentho,lencom1)])) if lentho else truncargs
										earlyabort = False
										# yasatflat = yasat.flatten(ScopeDelta([]),yoks[k][1].si)
										obj,ntyp = yoks[k][1].obj.verify(yfactor,reqtype=True)
										obj  =  obj.addlambdasphase2(yoks[k][1].si,pos=yoks[k][1])
										ntyp = ntyp.addfibration(truncargs)
										yoks[k] = (yoks[k][0],obj.dpush(ScopeDelta([(-lentho,lencom1)])),ntyp.dpush(ScopeDelta([(-lentho,lencom1)])))

										# print("assigned: ",row.name)
										# print("assigned: ",indesc.flat[len(indesc.flat)-lentho-1+yoks[k][0][0]])
										st = len(yoks)
										obj = implicitcast(indesc,rowtype,ntyp,obj,blame=yoks[k][1],soften=earlyabort,extract=yoks,thot=thot,odsc=lencom1,owner=trail+[n])
										ming = getming(thot,st)
										if ming!=None: return restart()
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
				moro,earlyabort = rowtype.compacrecurse(yoks,trail+[n],thot,indesc,delta,then=False,earlyabort=earlyabort)
				if type(moro) is int:#this is broken...?????
					if moro == 0:
						return reassembled.compacrecurse(yoks,trail,prep,startindesc,startdelta,then=then,earlyabort=earlyabort)
					return (moro-1,earlyabort)
				obj = SubsObject(verdepth=len(indesc)) if moro.isemptytype() else None
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				cu.append(TypeRow(row.name,rowtype,obj,self.rows[n].silent))
			thot = thot+namerical(len(indesc),self.rows[n].name,trail+[n])
			if type(self.rows[n].name) is not list:
				insf = TypeRow(self.rows[n].name,rowtype,obj,self.rows[n].silent)
				if obj!=None and self.rows[n].obj == None: delta = delta + ScopeDelta([([(len(indesc),obj)],)])
				indesc = indesc.sneakadd(ScopeObject([insf]))
			else:
				if obj!=None and self.rows[n].obj == None: delta = delta + ScopeDelta([(longflattenunravel(self.rows[n].name,rowtype,obj,len(indesc))[0],)])
				indesc = indesc.sneakadd(self.rows[n].type.flatten(ScopeDelta([]),self.rows[n].name,obj=obj))
		for n in range(len(self.rows)):
			for yok in yoks:
				if yok[0] == trail+[n] and cu[n].obj==None:
					raise CouldNotDeduceType(yok[1]).addparameterdata(yoks,trail+[n],len(thot),None,indesc).soften(earlyabort)
					# raise LanguageError(yok[1],"Cannot infer type of parameter.")
		outp = DualSubs(cu,verdepth=self.verdepth,pos=self)
		return ((outp,earlyabort),(indesc,delta)) if then else (outp,earlyabort)

	def applytemplate(self,indesc,NSC,subs,rows,blame=None,shortname=None,secret=None):
		poppo = [(NSC[0][a],NSC[1][a]) for a in range(len(NSC[0]))]
		inc = []
		def triplecopy(ma):
			if type(ma) is list: return [triplecopy(k) for k in ma]
			for swap in range(len(poppo)):
				if poppo[swap][0]==ma:
					res = poppo[swap][1]
					for j in range(longcount(poppo[swap][1])):
						inc.append(True)
					del poppo[swap]
					return res
			inc.append(False)
			return ma

		def secretoken(secret,wlist,stdep,endep,tail=None):
			acu = []
			for w in range(len(wlist)):
				ka = wlist[w][0].dpush(ScopeDelta([(endep+w-wlist[w][0].type.verdepth,wlist[w][0].type.verdepth)]))
				if ka.obj==None:
					acu.append(TypeRow(ka.name,ka.type,RefTree(stdep+w,verdepth=ka.type.verdepth),ka.silent))
				else:
					acu.append(ka)
			if tail!=None:
				acu.append(tail.dpush(ScopeDelta([(len(acu),endep)])))
			sj = TypeRow(secret[1],DualSubs(acu,verdepth=self.verdepth+len(wlist)),SubsObject(verdepth=self.verdepth+len(wlist)))
			if secret[0]!=None:
				return secretoken(secret[0][0],secret[0][1],stdep-len(wlist),endep,tail=sj)
			return sj
	


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

		def shape1(wclist,a):
			tub = []
			wlist = []
			sources = []
			for b in range(len(wclist)):
				if b!=a and wclist[a][2] not in wclist[b][3]:
					wlist.append((wclist[b][0].dpush(ScopeDelta(tub)),wclist[b][1],wclist[b][2],wclist[b][3]))
					sources.append(b)
				else:
					tub.insert(0,(-1,self.verdepth+b))
			return (sources,wlist)
		def addrefs(wclist,sources,a,token):
			hs = self.verdepth
			for b in sources:
				if wclist[b][2] not in wclist[a][3] and wclist[a][2] not in wclist[b][3]:
					if wclist[b][0].obj==None and token.detect(ScopeDelta([(-1,hs)])):
						wclist[a][3].append(wclist[b][2])
						for c in wclist[b][3]:
							if c not in wclist[a][3]: wclist[a][3].append(c)
						for c in range(len(wclist)):
							if wclist[a][2] in wclist[c][3]:
								for d in wclist[a][3]:
									if d not in wclist[c][3]: wclist[c][3].append(d)
				hs+=1
		def shape2(sources,wlist,wclist,converter):
			# print("shape2")
			assert len(sources)==len(wlist)
			dbgname = wclist[sources[-1]][0].name
			for b in range(len(wclist)):
				if b not in sources: sources.append(b)
			assert len(sources)==len(wclist)
			for b in range(len(wlist),len(wclist)):
				tub1 = []
				tub3 = []
				hacakewalk = copy.copy(sources[:b])
				for c in reversed(range(b)):
					if sources[b]<sources[c]:
						tub1.insert(0,(1,self.verdepth+c))
						del hacakewalk[c]
				def _dbgTest():
					for c in sources[b+1:]:
						if sources[b]>c:
							assert False
				# for c in range(len(hacakewalk)):
				# 	for d in range(c):
				# 		if hacakewalk[c]<hacakewalk[d]:    #c > d
				# 			if hacakewalk[d]<sources[b]:
				# 				tub3.append((self.verdepth+hacakewalk[c],1,self.verdepth+hacakewalk[d],1))
				# 			swp = hacakewalk[c]
				# 			hacakewalk[c] = hacakewalk[d]
				# 			hacakewalk[d] = swp
				for d in range(len(hacakewalk)-1):
					c = d
					for m in range(d+1,len(hacakewalk)):
						if hacakewalk[m]<hacakewalk[c]: c=m
					if c!=d:
						tub3.append((self.verdepth+hacakewalk[c],1,self.verdepth+hacakewalk[d],1))
						swp = hacakewalk[c]
						hacakewalk[c] = hacakewalk[d]
						hacakewalk[d] = swp
				tub = tub3+tub1
				# print("-=-=-=-=-=-=-=-=-=-")
				# print("\n"*5)
				# print(wclist[sources[b]][0])
				# print("\t",dbgname,wclist[sources[b]][0].name)
				# print("\t",tub)
				# print("\t",converter.pushes[0][0][0][0])
				wlist.append((wclist[sources[b]][0].dpush(ScopeDelta(tub)+converter),wclist[sources[b]][1],wclist[sources[b]][2],wclist[sources[b]][3]))
		def correctness(lis):

			for a in range(len(lis)):
				for b in range(a):
					assert lis[a][2]!=lis[b][2]

			for i in range(len(lis)):
				for a in range(len(lis[i][3])):
					for b in range(a):
						assert lis[i][3][a]!=lis[i][3][b]

				for ref in lis[i][3]:
					for j in range(i):
						if lis[j][2]==ref:
							for ref2 in lis[j][3]:
								assert ref2 in lis[i][3]
							break
					else: assert False
		def tightcorrectness(lis):
			correctness(lis)
			indesc.addflat(ScopeObject([k[0] for k in lis]))
			for k in range(len(lis)):
				for h in range(k):
					if lis[h][0].obj==None:
						a = lis[k][0].obj!=None and lis[k][0].obj.detect(ScopeDelta([(-1,self.verdepth + h)]))
						c = lis[k][0].type.detect(ScopeDelta([(-1,self.verdepth + h)]))
						b = (lis[h][2] in lis[k][3])
						# print("ab",a,b,lis[h][0].name,lis[k][0].name)
						if (c or a) and not b:
							print("C",c)
							print("A",a)
							print("ind",k,lis[k][0].name)
							print("h",h,lis[h][0].name)
							assert False

		dn = copy.copy(subs)
		while len(dn):
			if dn[0].name!=None and dn[0].name[0] in dn: continue
			for origindex in range(len(wclist)):
				a=0
				while wclist[a][2]!=origindex+self.verdepth: a+=1
				if dn[0].name==None or (wclist[a][0].obj==None or len(dn[0].name)==1) and dn[0].name[0]==wclist[a][0].name:
					# everything without a ref | everything with a ref.
					sources,wlist = shape1(wclist,a)
					wonk = indesc.addflat(ScopeObject([w[0] for w in wlist])).prepushPR(ScopeDelta([(1,indesc.beginlen()+n) for n in range(len(wlist)) if not wlist[n][1]]))
					ltype = wclist[a][0].type.dpush(ScopeDelta([(len(wlist)-a,self.verdepth+a)]))

					if dn[0].name==None or len(dn[0].name)==1:
						if secret!=None:
							wonk = wonk.invisadd(ScopeObject([secretoken(secret,wlist,self.verdepth,self.verdepth+len(wlist))]))

						if wclist[a][0].obj==None:
							print("B1")

							yarn = TypeRow(wclist[a][0].name,ltype,dn[0].obj.verify(wonk,ltype),wclist[a][0].silent)
							addrefs(wclist,sources,a,yarn.obj)
							converter = ScopeDelta([
								([(len(indesc)+len(wlist),yarn.obj)],)
							])
							wlist.append((yarn,wclist[a][1],wclist[a][2],wclist[a][3]))
							sources.append(a)
							shape2(sources,wlist,wclist,converter)
							wclist=wlist

						else:

							print("B2")
							# thot (in) ---> (name of token,unique identifier of replacement)
							# extract (out) <--- (unique identifier,token,True)

							extract = []
							lobj = wclist[a][0].obj.dpush(ScopeDelta([(len(wlist)-a,self.verdepth+a)]))
							# def _dbgTest():
							# 	assert not lobj.detect(ScopeDelta([(len(wlist)-a,self.verdepth+a)]))

							lobj.compare(dn[0].obj.verify(wonk,ltype),len(indesc)+len(wlist),[(len(indesc)+i,i) for i in range(len(wlist))],extract)
							gather = []
							origsources = sources
							while len(extract):
								i = 0
								while True:
									for l in range(len(extract)):
										if wlist[extract[i][0]][2] in wlist[extract[l][0]][3]:
											i = l
											break
									else: break
								r = extract[i]
								del extract[i]
								sources2,gnlist = shape1(wlist,r[0])
								try:
									takenout = r[1].dpush(ScopeDelta([( -1,len(indesc)+i) for i in reversed(range(len(origsources))) if i not in sources2]))
								except DpushError:
									raise LanguageError(blame,"Equivalence statement cannot be made true without creating a cyclic reference.")
								addrefs(wclist,[origsources[i] for i in sources2],sources[r[0]],takenout)
								converter = ScopeDelta([([(len(indesc)+len(gnlist),takenout)],)])
								omtype = wlist[r[0]][0].type.dpush(ScopeDelta([(len(gnlist)-r[0],self.verdepth+r[0])]))
								gather.append(wlist[r[0]][2])
								gnlist.append((TypeRow(wlist[r[0]][0].name,omtype,takenout,wlist[r[0]][0].silent),wlist[r[0]][1],wlist[r[0]][2],wlist[r[0]][3]))
								sources2.append(r[0])
								shape2(sources2,gnlist,wlist,converter)
								wlist=gnlist
								enext = []
								for e in extract:
									for i in range(len(sources2)):
										if sources2[i]==e[0]:
											enext.append((i,e[1]))
											break
									else: assert False
								extract = enext
								sources=[sources[i] for i in sources2]
							converter = ScopeDelta([([
								(self.verdepth + n,wlist[n][0].obj) for n in range(len(wlist)) if wlist[n][2] in gather
							],)])
							shape2(sources,wlist,wclist,converter)
							wclist=wlist
						del dn[0]
					else:

						print("B3")
						ty = ltype.decode()
						if type(ty) is RefTree: ty = ty.mangle_UE()
						if type(ty) is not DualSubs: raise LanguageError(blame,"Tried to subaccess thing that doesn't have subproperties "+str(dn[0].name))
						desc = []
						for o in reversed(range(len(dn))):
							if dn[o].name!=None and dn[o].name[0]==wclist[a][0].name and len(dn[o].name)>1:
								desc.append(SubRow(dn[o].name[1:],dn[o].obj))
								del dn[o]
						hab = (None,wclist[a][0].name) if secret==None else ((secret,wlist),wclist[a][0].name)
						yarn = TypeRow(wclist[a][0].name,ty.applytemplate(wonk,([],[]),desc,[],blame=blame,shortname=ltype,secret=hab),None,wclist[a][0].silent)
					
						addrefs(wclist,sources,a,yarn.type)
						b = self.verdepth+len(wlist)
						converter = ScopeDelta([
							(1,b),
							([(
								b+1,
								implicitcast(
									None,
									ltype.dpush(ScopeDelta([(1,b)])),
									yarn.type.dpush(ScopeDelta([(1,b)])),
									RefTree(b,verdepth=b+1)
								)
							)],),
							(-1,b+1)
						])
						wlist.append((yarn,wclist[a][1],wclist[a][2],wclist[a][3]))
						sources.append(a)
						shape2(sources,wlist,wclist,converter)
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
	def assertcomp(self,other):
		assert type(other) is SubsObject
		assert len(self.subs) == len(other.subs)
		for a in range(len(self.subs)):
			assert self.subs[a].name == other.subs[a].name
			self.subs[a].obj.assertcomp(other.subs[a].obj)


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
		return SubsObject([SubRow(None,k.obj.dpush(pushes,exob=exob)) for k in self.subs],pos=self,verdepth=self.verdepth+pushes.lenchange())

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else rigpush+other.correction())
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
		carry = carry.decode()
		if type(carry) is not DualSubs:
			ocarry = carry.mangle_UE() if type(carry) is RefTree else None
			if type(ocarry) is not DualSubs: raise NonUnionTypeError(self,carry,indesc)
			carry = ocarry

		oflow = []
		garbo = carry.compacassign(self.phase1(indesc),overflow=oflow)
		if len(oflow): raise VariableAssignmentError(self,oflow[0][0])

		try:
			st = carry.peelcompactify(indesc,garbo,earlyabort=False)[0]
			ga = st.extractbetween(carry,blame=self)
		except LanguageError as u:
			u.callingcontext([("(Constructing element of union)",carry,len(indesc),indesc,None)],0)
			raise u
		return SubsObject(ga,verdepth=len(indesc),pos=self)

class Template(Tobj):
	@initTobj
	def __init__(self,src,NSC=None,rows=None,subs=None,pos=None):
		# assert type(subs) is SubsObject
		self.NSC = ([],[]) if NSC==None else NSC
		self.rows = [] if rows == None else rows
		self.subs = [] if subs == None else subs
		self.src = src
		transferlines(self,pos)
	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assert not then
		assertstatequal(indesc,self,carry,u_type(len(indesc)))
		src = self.src.verify(indesc,u_type(len(indesc)))
		osrc = src
		src = src.decode()
		if type(src) is RefTree: src = src.mangle_UE()
		if type(src) is not DualSubs:
			raise LanguageError(self,"Can only apply templating to {"+"} object.")
		if len(self.NSC[0])!=len(self.NSC[1]):
			raise LanguageError(self,"Renaming statements must have an equal number of names on both sides.")
		for k in self.NSC[0]:
			if type(k) is list: raise LanguageError(self,"You can't recursively nest renaming statements on the left.")
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


def correctLambda(si,obj,inp,verdepth=None,pos=None):
	def smush(tok):
		if type(tok) is list:
			res = ""
			for t in tok: res = res + smush(t)
			return res
		return tok
	delta = inp
	for s in range(len(si)):
		if type(si[s]) is list:
			vv = longcount(si[s])
			delta = delta + ScopeDelta([
				(1,verdepth+s),
				(coflattenunravel(si[s],RefTree(verdepth+s,verdepth=verdepth+s+1),verdepth+s+1),),
				(-vv,verdepth+s+1)
			])
	return Lambda([smush(s) for s in si],obj if delta.isempty() else obj.dpush(delta),verdepth=verdepth,pos=pos)


class Lambda(Tobj):
	def assertcomp(self,other):
		assert type(other) is Lambda
		assert self.si == other.si
		self.obj.assertcomp(other.obj)


	@initTobj
	def __init__(self,si,obj,verdepth=None,pos=None):
		self.si = si
		# assert len(si)>0
		self.obj = obj
		self.verdepth = verdepth
		transferlines(self,pos)
		def _dbgTest():
			if verdepth!=None:
				assert all(type(s) is not list for s in si)
		# if verdepth!=None:
		# 	self.verdepth = verdepth
		# 	self.complexity = 1+self.obj.complexity
		# 	self.touches = {k for k in self.obj.touches if k<verdepth}
		# 	self.softtouches = {k for k in self.obj.softtouches if k<verdepth}
	def writefile(self,file):
		file.writeChar("G")
		file.writeStrInc(self.si)
		self.obj.writefile(file)

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
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else rigpush+other.correction())
		if type(other) is RefTree: other = other.unwrap()
		if (type(other) is not Lambda or len(self.si)!=len(other.si)) and type(self.obj) is ScopeComplicator:
			return self.obj.decode().addlambdasphase2(self.si).compare(other,odsc,thot,extract,lefpush,rigpush)
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
		if type(self.obj) is ScopeComplicator and not context.printcomplicators:
			return self.obj.decode().addlambdasphase2(self.si).prepr(context)
		if type(self.obj) is RefTree and self.obj.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.obj.name)):
			return self.obj.unwrapOne().addlambdasphase2(self.si).prepr(context)
		word = context.newcolors(self.si)
		return pmultilinelist(self.si,context,word)+self.obj.prepr(context.addbits(word))
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		if type(self.obj) is ScopeComplicator and not context.printcomplicators:
			return self.obj.decode().addlambdasphase2(self.si).pmultiline(context,out,indent,prepend,postpend,callback=callback)
		if type(self.obj) is RefTree and self.obj.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.obj.name)):
			return self.obj.unwrapOne().addlambdasphase2(self.si).pmultiline(context,out,indent,prepend,postpend,callback=callback)
		word = context.newcolors(self.si)
		self.obj.pmultiline(context.addbits(word),out,indent,prepend+pmultilinelist(self.si,context,word),postpend,callback)
class Strategy(Tobj):

	def assertcomp(self,other):
		assert type(other) is Strategy
		self.args.assertcomp(other.args)
		self.type.assertcomp(other.type)


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

	def getbecsafety(self):
		if hasattr(self,'becsafety'): return self.becsafety
		return len(self.args)

	def writefile(self,file):
		file.writeChar("E")
		self.args.writefile(file,shutup=True)
		self.type.writefile(file)


	def detect(self,ranges):
		return self.args.detect(ranges) or self.type.detect(ranges)

	def dpush(self,pushes,exob=None):
		disgrace = ScopeDelta()
		newargs = self.args.dpush(pushes,disgrace=disgrace)
		newtype = self.type.dpush(disgrace+pushes)
		dis = newtype.addfibration(newargs,pos=self)
		return dis

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else rigpush+other.correction())
		if type(other) is RefTree:
			att = other.mangle_FE()
			if att!=None: return self.compare(att,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not Strategy: return False


		if len(other.args)<len(self.args) and type(other.type) is ScopeComplicator:
			return self.compare(other.type.decode().addfibration(other.args),odsc,thot,extract,lefpush,rigpush)
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


		return correctLambda([k.name for k in trimargs.rows],tat,ScopeDelta(),verdepth=limit)

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
			vertype = self.type.verify(thendesc,carry.dpush(ScopeDelta([(longcount(verargs),len(indesc))])),reqtype=reqtype,then=then)
			# return vertype.dpush(ScopeDelta([(-longcount(verargs),len(indesc))]))
			rip = verargs.rip()
			if reqtype:
				verobj,vertype = vertype
				verobj = complicate(verobj,rip,pos=self)
				vertype = complicate(vertype,rip,pos=self)
				verobj.legaltracking=False
				return verobj,vertype
			mou = complicate(vertype,rip,pos=self)
			mou.legaltracking=False
			return mou

		assertstatequal(indesc,self,carry,u_type(len(indesc)))
		vertype = self.type.verify(thendesc,u_type(len(thendesc)))
		outp = vertype.addfibration(verargs)

		return (outp,u_type(len(indesc))) if reqtype else outp
	def prepr(self,context):
		if type(self.type) is ScopeComplicator and not context.printcomplicators:
			return self.type.decode().addfibration(self.args).prepr(context)
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
		if type(self.type) is ScopeComplicator and not context.printcomplicators:
			return self.type.decode().addfibration(self.args).pmultiline(context,out,indent,prepend,postpend,callback=callback)
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
	def assertcomp(self,other):
		assert type(other) is RefTree
		assert self.name == other.name
		assert (self.src==None) == (other.src==None)
		if self.src!=None: self.src.assertcomp(other.src)
		self.args.assertcomp(other.args)

	@initTobj
	def __init__(self,name=None,args=None,src=None,verdepth=None,pos=None,core=None):
		self.name       = 0 if name == None else name
		self.args       = SubsObject(verdepth=verdepth) if args == None else args
		self.src        = src
		self.core       = core
		self.verdepth   = verdepth

		transferlines(self,pos)
		def _dbgTest():
			assert type(self.name) is int or type(self.name) is str
			if self.src==None and self.verdepth!=None and self.name!=0:
				assert self.name<self.verdepth
			assert type(self.args) is SubsObject
			if self.core!=None:
				assert self.core.isSubOb != self.name
				# print()
			if self.src!=None:
				assert type(self.src) is not SubsObject
				assert type(self.src.isSubOb()) is not bool or not self.src.isSubOb()
				if self.src.isSubOb() and type(self.src.isSubOb()) is bool:
					assert False


			# if self.core!=None:
			# 	if type(self.core.core) is RefTree and self.core.core.name==:
			# 		assert 
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


	def unwrap(self):
		if self.core==None: return self
		ja = self.unwrapOne()
		if type(ja) is ScopeComplicator: ja = ja.decode()
		if type(ja) is RefTree: ja = ja.unwrap()
		return ja

	def unwrapOne(self):
		if len(self.args.subs)==0:
			if self.core.rows.isempty():
				return self.core.core
			am = self.core.core.dpush(self.core.rows).decode()
			self.core.core = am
			self.core.rows = ScopeDelta()
			return am
		return self.core.core.dpush(self.core.rows,exob=self.args).decode()

	def detect(self,ranges):
		if self.core!=None:
			if self.args.detect(ranges): return True
			if hasattr(ranges,'precal') and self.name in ranges.precal: return False
			if ranges.islowerbound(self.name): return False
			if self.core.core.detect(self.core.rows + ranges): return True#<><><> account for special case
			if not hasattr(ranges,'precal'): ranges.precal = []
			ranges.precal.append(self.name)
			return False
		if self.src==None:
			if not ranges.canTranslate(self.name,self.verdepth): return True
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
				outp = RefTree(src=outp,args=decargs,name=self.name,verdepth=outp.verdepth,pos=self)
			else:
				outp = outp.reference(self.name)
				if len(decargs.subs): return outp.dpush(ScopeDelta(),exob=decargs)
			return outp
		if self.name!=0:
			if self.core!=None and not pushes.canTranslate(self.name,ignoresubs=True):
				decargs = self.args if pushes.isempty() else self.args.dpush(pushes)
				if exob != None: decargs = SubsObject(decargs.subs+exob.subs,verdepth=pushdepth)
				return self.core.core.dpush(self.core.rows+pushes,decargs if len(decargs.subs) else None)
			gy = pushes.translate(self.name,ignoresubs=self.core!=None)
		if type(gy) is int:
			decargs = self.args if pushes.isempty() else self.args.dpush(pushes)
			if exob != None: decargs = SubsObject(decargs.subs+exob.subs,verdepth=pushdepth)
			return RefTree(gy,decargs,None,pos=self,verdepth=pushdepth,core=None if self.core==None else self.core.dpush_ds(pushes))
		elif len(gy)==3:
			# teleport
			# (j[2],ScopeDelta(self.pushes[:i]),ScopeDelta(self.pushes[i+1:]))
			# print(gy[0][0].verdepth<self.verdepth)
			# print(gy[0][0].verdepth>self.verdepth+gy[1].lenchange())
			# def _dbgTest():
			# 	assert gy[0][0].verdepth>self.verdepth+gy[1].lenchange()
			pard = self.dpush(gy[1]+ScopeDelta([(gy[0][0].verdepth-(self.verdepth+gy[1].lenchange()),gy[0][0].verdepth)]))
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

			if not gy[1].canTranslate(gy[2],ignoresubs=True):
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
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else rigpush+other.correction())
		if self.src != None:
			if type(other) is not RefTree: return False
			if other.src==None: other = other.unwrap()
			if type(other) is not RefTree: return False
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
					def _dbgTest():
						other.setSafety(dsc-(0 if rigpush==None else rigpush.lenchange()))
					try:
						gr = other.dpush((ScopeDelta() if rigpush==None else rigpush) + (ScopeDelta([(odsc-dsc,odsc,repls)]) if len(repls) else ScopeDelta([(odsc-dsc,odsc)])))
					except DpushError:
						print("there was a dpusherror preventing: ",self)
						print("\t",other)
						# print("\t",other.prepr(FormatterObject(None,fullrepresent=True)))
						return False
					def _dbgTest():
						gr.setSafety(odsc+len(repls))
					mod = gr.addlambdasphase2(["_"]*len(repls))
					def _dbgTest():
						mod.setSafety(odsc)
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(mod)
					extract.append((k[1],mod,True))
					return True
		if self.core==None and type(other) is RefTree and other.core!=None:

			return self.compare(other.unwrap(),odsc,thot,extract,lefpush,rigpush)

			# other=other.unwrap()
			# while type(other) is ScopeComplicator:
			# 	rigpush = other.correction() if rigpush==None else rigpush+other.correction()
			# 	other = other.core
		if self.core!=None and (type(other) is not RefTree or other.core==None): return self.unwrap().compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is Strategy: 
			att = self.mangle_FE()
			if att==None:
				natt = other.reverse_mangle_FE()
				if natt==None: return False
				return self.compare(natt,odsc,thot,extract,lefpush,rigpush)
			
			va = att.compare(other,odsc,thot,extract,lefpush,rigpush)
			print("hypothesis ",va)
			if not va:
				print(att)
				print(other)
			return va
		if type(other) is DualSubs:
			att = self.mangle_UE()
			if att==None: return False
			return att.compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not RefTree or other.src!=None:
			
			return False
		if self.core==None and other.core==None:
			return (self.name if lefpush==None else lefpush.translate(self.name))==(other.name if rigpush==None else rigpush.translate(other.name)) and self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush)
		aH=self
		bH=other
		a = []
		b = []
		while True:
			if type(aH) is RefTree and aH.core!=None:
				if lefpush==None or lefpush.canTranslate(aH.name):
					aname = aH.name if lefpush==None else lefpush.translate(aH.name)
					for g,bname in b:
						if aname==bname:
							if aH.args.compare(g.args,odsc,thot,extract,lefpush,rigpush): return True#<><><> special case here... (arg order invariant or unused.)
					a.append((aH,aname))
					aH = aH.unwrapOne().decode()
				else:
					aH = aH.unwrapOne().decode()
			if type(bH) is RefTree and bH.core!=None:
				if rigpush==None or rigpush.canTranslate(bH.name):
					bname = bH.name if rigpush==None else rigpush.translate(bH.name)
					for g,aname in a:
						if aname==bname:
							if g.args.compare(bH.args,odsc,thot,extract,lefpush,rigpush): return True#<><><> special case here... (arg order invariant or unused.)
					b.append((bH,bname))
					bH = bH.unwrapOne().decode()
				else:
					bH = bH.unwrapOne().decode()
			if (type(aH) is not RefTree or aH.core==None) and (type(bH) is not RefTree or bH.core==None):
				return aH.compare(bH,odsc,thot,extract,lefpush,rigpush)



	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assert not then
		p1 = self.args.phase1(indesc)
		errorcontext = []
		if self.src == None:
			tra = indesc.symextract(self.name,p1,carry=carry,reqtype=reqtype,pos=self,errorcontext=errorcontext)
			if tra != None: return tra
			for a in range(len(indesc.flat)):
				if indesc.flat[a].name==self.name and (-indesc.prepushes).canTranslate(a):
					raise LanguageError(self,"Symbol not defined for these arguments: "+self.name).callingcontext(errorcontext,-1)
			raise LanguageError(self,"Symbol not defined in this context: "+self.name).callingcontext(errorcontext,-1)
		else:
			if self.src.needscarry(): raise LanguageError(self,"Need to be able to generate type for property access...")
			orig = self.src.verify(indesc,reqtype=True)
			examtype = orig[1].decode()
			examtype = examtype.mangle_UE() if type(examtype) is RefTree else examtype
			if examtype!=None and type(examtype) is DualSubs:

				anguish = examtype.flatten(ScopeDelta([]),obj=orig[0])
				tra = indesc.invisadd(anguish).preerase(len(anguish)).symextract(self.name,p1,carry=carry,reqtype=reqtype,limiter=len(indesc.flat),pos=self,errorcontext=errorcontext)
				if tra != None: return tra

			possib = orig[0].decode()
			while type(possib) is RefTree:
				if possib.src == None:

					retrievalname = indesc.flat[(-indesc.postpushes).translate(possib.name)].name
					print("RETRIEVALNAME: ",retrievalname,self.name)

					tra = indesc.symextract(retrievalname+"."+self.name,possib.args.phase1_gentle()+p1,reqtype=reqtype,carry=carry,pos=self,cosafety=len(possib.args.subs),errorcontext=errorcontext)
					if tra != None: return tra
				if possib.core==None: break
				possib = possib.unwrapOne()

			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,carry=carry,pos=self,errorcontext=errorcontext)
			if tra != None: return tra
			raise LanguageError(self,"Symbol not defined for these arguments as a property access, macro, or operator overload: "+self.name).callingcontext(errorcontext,-1)
	def prepr(self,context):
		if self.core!=None and (context.fullrepresent or not context.forbiddenrange.canTranslate(self.name)):
			return self.unwrapOne().prepr(context)
		# if self.core!=None: return self.unwrap().prepr(context)
		res = str(context.getname(self.name)) if self.src==None else str(self.name)
		if self.src != None:
			res = self.src.prepr(context)+"."+res
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
		else:
			self.src.pmultiline(context,out,indent,prepend,".",callback=calls)


	def mangle_FE(self):
		component = self.unwrap().decode()
		if type(component) is not RefTree: return component
		if component.name==1 and component.src==None:
			jab = component.args.subs[0].obj.decode()
			if type(jab) is RefTree: jab = jab.mangle_FE()
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
		component = self.unwrap().decode()
		if type(component) is not RefTree: return component
		if component.name==1 and component.src==None:
			jab = component.args.subs[0].obj.decode()
			if type(jab) is RefTree: jab = jab.mangle_UE()
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
										SubRow(None,correctLambda([thad[0],"_"],nurows[-1],ScopeDelta([(1,nurows[-1].verdepth)]),verdepth=alc)),
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
										SubRow(None,correctLambda([thad,"_"],nurows[-1],ScopeDelta([(1,nurows[-1].verdepth)]),verdepth=alc)),
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
					while len(shift[-1]) == 3 and shift[-1][1] < prec or shift[-1][1] == prec and not nesting:
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
			errorcontext=[]
			ghi = indesc.symextract(tree[0],p1,reqtype=True,carry=carry,pos=self,errorcontext=errorcontext)
			if ghi == None:
				if len(errorcontext)==0:
					raise LanguageError(self,"operator not defined: "+str(tree[0]))
				raise LanguageError(self,"operator not defined for these arguments: "+str(tree[0])).callingcontext(errorcontext,-1)
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

def complicate(core,secrets,pos=None):
	if len(secrets):
		return ScopeComplicator(core,secrets,verdepth=core.verdepth-len(secrets),pos=pos)
	return core

def semi_complicate_dpush(depth,secrets,pushes):
	res = []
	sof = ScopeDelta()
	s = depth
	for secret in secrets:
		try:
			res.append(secret.dpush(pushes+sof))
			s+=1
		except DpushError:
			sof.append((-1,s))

			# dont hate me for this but i think dpusherror lazy evaluation only works with 3s...<><><><><>

	return res,sof

class ScopeComplicator(Tobj):
	@initTobj
	def __init__(self,core,secrets,verdepth=None,pos=None):
		self.core = core
		self.secrets = secrets
		self.verdepth = verdepth
		self.legaltracking = True
		transferlines(self,pos)
		def _dbgTest():
			assert type(self.secrets) is list
			assert len(self.secrets)

	def correction(self):
		return ScopeDelta([(-len(self.secrets),self.verdepth)])
	def decode(self):
		if not self.legaltracking: assert False
		return self.core.dpush(self.correction()).decode()
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		return self.core.compare(other,odsc,thot,extract,self.correction() if lefpush==None else lefpush+self.correction(),rigpush)
	def dpush(self,pushes,exob=None):
		res,sof = semi_complicate_dpush(self.verdepth+pushes.lenchange(),self.secrets,pushes)
		return complicate(self.core.dpush(pushes+sof,exob=exob),res,pos=self)


	def detect(self,ranges):
		return self.core.detect(ranges)
	def writefile(self,file):
		file.writeChar("J")
		file.writeNum(len(self.secrets))
		for secret in self.secret:
			secret.writefile(file)

	def prepr(self,context):
		if not context.printcomplicators: return self.decode().prepr(context)
		res = []
		for k in self.secrets:
			word = context.newcolors(None)
			res.append(k.prepr(context))
			context = context.addbits(word)
		return context.red("[[[")+",".join(res)+context.red("]]]")+self.core.prepr(context)
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		if not context.printcomplicators: return self.decode().pmultiline(context,out,indent,prepend,postpend,callback=callback)
		def calls(context,out,prepend):
			self.core.pmultiline(context,out,indent,prepend,postpend,callback=callback)
		pmultilinecsv(context,out,indent,self.secrets,prepend+context.red("[[["),context.red("]]]"),lamadapt=lambda x:None,callback=calls,delim=context.red(","))



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
			if type(children[1]) is Strategy: children[0][1]['contractible'] = children[1].getbecsafety()
			return TypeRow(children[0][0],children[1],obj,children[0][1])
		obj = None
		if len(children)>1:
			obj = children[1]
			# if type(children[0]) is Strategy:
			# 	obj = Lambda(children[0].args.semavail(),obj,pos=meta)
		return TypeRow(None,children[0],obj,{'silent':False,'contractible':None if type(children[0]) is not Strategy else children[0].getbecsafety()})
	def inferreddeclaration(self,children,meta):
		ty = None if len(children)<3 else Strategy(args=children[1],type=None,pos=meta)
		if type(ty) is Strategy: children[0][1]['contractible'] = ty.getbecsafety()
		return TypeRow(children[0][0],ty,children[-1],children[0][1])
	def silentmarker(self,children,meta):
		return {'silent':True,'contractible':None}
	def infermarker(self,children,meta):
		return {'silent':False,'contractible':None}
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
		args = []
		for j in children[lim:]:
			args += j.subs
		return RefTree(name,SubsObject(args,pos=meta),src,pos=meta)
	def lamb(self,children,meta):
		coal = []
		for c in children[:-1]:
			coal+=c
		return Lambda(coal,children[-1],pos=meta)
	def directive(self,children,meta):
		if len(children) == 1:
			return (children[0],children[0])
		return (children[0],children[1])
	def renamer(self,children,meta):
		return ([j for l in children for j in l[0]],[j for l in children for j in l[1]])
	def template(self,children,meta):
		if   len(children)==1: return Template(children[0],pos=meta)
		elif len(children)==3: return Template(children[0],children[1],children[2][0],children[2][1],pos=meta)
		else: assert False
	def mixedsubs(self,children,meta):
		return ([c for c in children if type(c) is TypeRow],[c for c in children if type(c) is SubRow])

	def strategy(self,children,meta):
		args = []
		for j in children[:-1]:
			args += j.rows
		ouou = Strategy(DualSubs(args,pos=meta),children[-1],pos=meta)
		if len(children)>2: ouou.becsafety = len([i for i in children[0].rows if i.obj==None])
		return ouou
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

	def wsafesubsobject(self,children,meta):
		if len(children):
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
		return Untransformer(copy.copy(self.dict),self.head)
	def emptywrite(self,amt):
		return Untransformer(copy.copy(self.dict),self.head+amt)
	def getat(self,ind):
		if ind not in self.dict: return None
		ob = self.dict[ind]
		return DelayedSub(ob,ScopeDelta([(self.head-ob.verdepth,ob.verdepth)]))
	def objwrite(self,ty,ds,si):
		if ds==None:
			self.head += longcount(si)
			return
		shead = self.head
		if type(si) is not list:
			self.dict[self.head] = ds
			self.head+=1
		else:
			sel = ty.decode()
			if type(sel) is RefTree:  sel = sel.mangle_UE().decode()
			if type(sel) is Strategy: sel = sel.type.decode()
			if type(sel) is RefTree:  sel = sel.mangle_UE().decode()
			if type(sel) is not DualSubs: assert False
			assert len(sel.rows)==len(si)
			k=0
			for s in range(len(si)):
				if sel.rows[s].obj==None:
					self.objwrite(sel.rows[s].type,ds.reference(k),si[s])
					k+=1
				else:
					self.objwrite(sel.rows[s].type,sel.rows[s].obj,si[s])
		assert self.head == shead+longcount(si)


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
		elif code == "J": return self.ScopeComplicator(depth)
		else: assert False
	def TypeRow(self,depth):
		code = self.readChar()
		name = self.readStrInc() if code in 'acegi' else None
		ty   = self.generic(depth)
		obj  = self.generic(depth) if code in 'ab' else None
		silent   = code in 'ghij'
		contract = self.readNum() if code in 'efij' else None
		return TypeRow(name,ty,obj,{'silent':silent,'contractible':contract})

	def ScopeComplicator(self,depth):
		depth = depth.isolate()
		oh = depth.head
		lim = self.readNum()
		rows = []
		for row in range(lim):
			ob = self.generic(depth)
			rows.append(ob)
			depth.objwrite(None,ob,None)
		return ScopeComplicator(self.generic(depth),rows,verdepth=oh)

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
								print("beginning load: ",self.basepath+filename)
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
										fve.insert(i,self.deps[i])
										tub.append((hs,self.lengths[i]))
									hs += self.lengths[i]
								self.cumu += ver if len(tub)==0 else [a.dpush(ScopeDelta(tub)) for a in ver]
								self.lengths.append(len(ver))
								self.deps.append(filename)
								print("loaded: ",self.basepath+filename)
								return
		if os.path.exists(self.basepath+filename+".ver"): os.remove(self.basepath+filename+".ver")
		try:
			deps,rows,ob = MyTransformer().transform(self.lark.parse(document))
		except UnexpectedInput as u:
			u.file = filename
			raise u
		for dep in range(len(deps)):
			for d in range(dep):
				if deps[d] == deps[dep]: raise LanguageError(None,"Duplicate import").setfile(filename)
			self.load(deps[dep],circular+[filename])

		print("beginning verify: ",self.basepath+filename)
		olen = len(self.cumu)
		pexclude = []
		hs=0
		for dep in range(len(self.deps)):
			if self.deps[dep] in deps: hs+=self.lengths[dep]
			else: pexclude.append((self.lengths[dep],hs))
		try:
			obj,ncumu = ob.verify(ScopeObject(self.cumu,prpush=ScopeDelta(pexclude),oprows=ContextYam(rows)),then=True)
		except LanguageError as u: raise u.setfile(filename)
		DataBlockWriter(self.basepath+filename+".ver").writeHeader(md5,[(a,self.md5s[a]) for a in self.deps],[j for j in ncumu.flat[olen:]])
		print("verified: ",self.basepath+filename)
		self.cumu = ncumu.flat
		self.lengths.append(len(self.cumu)-olen)
		self.deps.append(filename)

		# def _dbgTest():
		# DataBlockWriter("temporary.ver").writeHeader(md5,[],self.cumu)
		# with open("temporary.ver","r") as f:
		# 	dbt = DataBlockTransformer(f.read(),0)
		# dbt.readHeader()
		# ver = dbt.readScope(Untransformer({}))
		# DualSubs(self.cumu).assertcomp(DualSubs(ver))
		# one = DualSubs(self.cumu).prepr(FormatterObject(None,fullrepresent=True))
		# two = DualSubs(ver).prepr(FormatterObject(None,fullrepresent=True))
		# if one != two:
		# 	print("\n\n"*5,one)
		# 	print("\n\n"*2,two)
		# 	assert False


		# print("cross verified ",len(self.cumu))

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
		FileLoader(verbose=True,basepath="/Users/parkerlawrence/dev/agi/",redoAll=True).load("grouptheory.ax")
	except LanguageError as u:
		u.tohtml()
		raise u
	# except LanguageError as u:
	# 	u.tohtml()
	# compilefiles({"builtin.ax"},redoAll=True)
	# print("debug")


#if mangle_ue starts taking up a lot of time, remember that you can store ful/semavail on a property so yo don't have ot unwrap<><><>
#you could also create a separate unwrap function for trimming and dpushing at the same time to avoid all those extra properties you dont need.<><><>

#about out of reftree early... (isSubOb)<>


#allow origin to be set to whatever object summoned it ---//> <><> that way you don't store dualsubs twice they tend to be bulky

#branching compare inside of reftree should erase from st/extract if a branch fails....<><><><>

#subsobject will need to redetect(tuple of src)                            on dpush...<>

#really should crack down on (0,x) depth pushes.

#<>make it so a.b macros work a little more dilligently...

#if the time spent inside the compare function accounts for a significant portion of the runtime, then you should implement a list of previous substitutions to compare instead
#	those ladders may be subbed out already. they vanish when dpush clobbers them.

#you need to fine-tune the operator precidence and associativity.

#<><>make your code fast


#rip doesnt work...<><><><><><><><><><><><><>
	#also add a secrets validator...<>


#><><><><>><><><>><> detect short circuiting needs to take away stuff that refers to stuff thats further down in a tree.
		#this needs to happen on complicators and strategies.


#be very careful about trimming things. best case scenario, only [] dualsubs can get trimmed away. <><><><><><><><>
			#use switch pushes instead of negative pushes when you can.<><><><><>
			#have a structure for introducing dummy variables into the scope.<><><><><><>
			#automatically figure out when you are killing the scope. insert the scope instead and turn it into a swap (?????? may be impossible.).


#swaps can be dangerous...<><><><>
	#swapping two elements can result in a cold sub that references something that is above it in depth...
	#need to <><<><><><> write a validator to make sure that key really is an upper bound...
	#it is okay in principle as long as the object in question could still possibly exist... use it responsibly.

#<><><> isSubOb should not call decode


#.dpush(ScopeDelta([(-<><><><><>


#5 occurances...

#      .dpush(ScopeDelta([(-        .append((-








#<><><> force flag that you copy instead of any(3) and that way except DpushError actually works.







