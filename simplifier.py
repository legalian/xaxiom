
import copy
from inspect import getfullargspec
from lark import Transformer, v_args, Tree, Lark
import hashlib
# import os.path
import os
import json



#R      - actual code
#F      - formalization
#[f:F]C - compiler-compliant formalization

#FC - compiler-compliant formalization

#RC 

#(FC -> RC)


#practice/proof of concept:
	#type theory self-formalization structures
	#solver algorithm that happens to comply to compilable appraiser

#important:
	#(real code) algorithm that takes structures that comply to compilable appraiser and produces C code.
	#formalization of compilable appraiser
	#solver algorithm that happens to both comply to compilable appraiser and produce results that are garunteed to comply to compilable appraiser


#bonus:
	#algorithm that takes structures that comply to compilable appraiser and produces C code.
	#language interpreter.
	#language representer

#treat singluar element when specifying dualsubs as (element).

depth = 0



if True:

	def pmultilinelist(lis,context):
		def ppri(sj):
			if type(sj) is not list: return str(sj)
			return context.orange("[")+",".join([ppri(k) for k in sj])+context.orange("]")
		if type(lis) is not list: return str(lis)
		return context.orange("|")+",".join([ppri(k) for k in lis])+context.orange("|")

	def pmultilinecsv(out,indent,lis,head,tail,context,lamadapt=None,callback=None,delim=","):
		ocontext = context
		if len(head)<context.magic:
			lisrepr = []
			for k in lis:
				lisrepr.append(k.prepr(context))
				if lamadapt!=None: context = context.addbits(lamadapt(k))
			comb = delim.join(lisrepr)
			if len(head)+len(comb)+len(tail)<context.magic:
				if callback == None:
					out.append("\t"*indent+head+comb+tail)
				else:
					callback(out,head+comb+tail,context)
				return
		out.append("\t"*indent+head)
		context = ocontext
		for k in range(len(lis)):
			lis[k].pmultiline(out,indent+1,"",delim if k<len(lis)-1 else "",context)
			if lamadapt!=None:
				context = context.addbits(lamadapt(lis[k]))
		if callback == None:
			out.append("\t"*indent+tail)
		else:
			callback(out,tail,context)


	def transferlines(self,pos):
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
		if type(jj) is LazyEvaluation: jj.unspool()
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




	def singularindesc(most):
		fod = most[-1]
		for i in reversed(range(len(most)-1)):
			fod = most[i].concatenate(fod)
		return fod


	def allbits(si):
		if type(si) is list: return [a for b in si for a in allbits(b)]
		return [si]


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
			for j in ahjs.rows:
				if type(j.type) is Strategy and j.type.type==None:
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
			just = None
			compen = 0
			for j in ahjs.rows:
				just = j.getSafetyrow()
				if just != None:
					downdeepverify(ahjs,just)
					return just-compen
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


# def translateOutOfTime(pushes):
# 	if len(pushes)>2: return pushes
# 	res = []
# 	for i in range(pushes):
# 		amt,lim = pushes[i]
# 		if amt>0: continue
# 		for j in reversed(range(i)):
# 			if lim-amt>=pushes[j][1]: continue
# 			if pushes[j][0]>0:
# 				if lim>pushes[i][0]+pushes[j][1]: lim-=pushes[j][0]
# 				else:
# 					if lim-amt<pushes[i][0]+pushes[j][1]:
# 						if lim<pushes[j][0]: amt -= pushes[j][0]
# 						else: amt += pushes[j][1]-lim
# 					else:
# 						if lim<pushes[j][0]:
# 							lim=pushes[j][1]
# 							amt+=lim-pushes[j][1]-pushes[j][0]
# 						else: amt=0
# 			else:
# 				if lim<pushes[j][1]: amt += pushes[j][0]
# 				else: lim -= pushes[j][0]
# 		assert amt>=0
# 		if amt>0:
# 			res.append((amt,lim))





def translateForward(fug,pushes):
	for amt,lim in pushes:
		if fug>=lim:
			fug+=amt
			if fug<lim: raise DpushError()
	return fug

def canTranslate(fug,pushes):
	for amt,lim in pushes:
		if fug>=lim:
			fug+=amt
			if fug<lim: return False
	return True

def canTranslateBackward(fug,pushes):
	for amt,lim in reversed(pushes):
		if fug>=lim:
			fug-=amt
			if fug<lim: return False
	return True


def translateForwardGentle(fug,pushes):
	# print("do better")
	return translateForward(fug,translateForwardGentlePreserve(fug,pushes))





def translateBackward(fug,pushes):
	for amt,lim in reversed(pushes):
		if fug>=lim:
			fug-=amt
			assert fug>=lim
	return fug

def translateForwardPreserve(fug,pushes):
	track = []
	for amt,lim in pushes:
		if fug>=lim:
			track.append((amt,lim))
			fug+=amt
			assert fug>=lim
	return track

def translateForwardGentlePreserve(fug,pushes):
	track = []
	for amt,lim in pushes:
		assert amt<=0
		if fug>=lim-amt: track.append((amt,lim))
		if fug>=lim: fug = max(fug+amt,lim)
	return track

def translateBackwardPreserve(fug,pushes):
	track = []
	for amt,lim in reversed(pushes):
		if fug>lim:
			fug-=amt
			assert fug>=lim
			track.insert(0,(amt,lim))
	return track






def _dbgEnter_dpush(self,pushes):
	self.setVerified()
	if type(self) is TypeRow or type(self) is SubRow or type(self) is LazyTypeRow:
		safe = self.getSafetyrow()
	else:
		safe = self.getSafety()
	if safe == None: return
	for amt,lim in pushes:
		assert lim<=safe
		assert lim-amt<=safe
		safe+=amt
def _dbgExit_dpush(self,pushes,outp):
	pamt = sum(j[0] for j in pushes)
	if type(self) is TypeRow or type(self) is SubRow or type(self) is LazyTypeRow:
		safe = self.getSafetyrow()
		outp.setSafetyrow(None if safe == None else safe+pamt)
	else:
		safe = self.getSafety()
		outp.setSafety(None if safe == None else safe+pamt)
		outp.setVerified()
def _dbgEnter_ddpush(self,amt,lim,repls,replsrc):
	self.setVerified()
	if type(self) is TypeRow or type(self) is SubRow or type(self) is LazyTypeRow:
		pass
	else:
		assert lim<=self.verdepth and lim-amt<=self.verdepth
	if repls!=None:
		for k in repls:
			k.setSafety(replsrc)
	assert amt<0




def _dbgEnter_pmultiline(self,out,indent,prepend,postpend,context,callback):
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
	lsum = 0 if lefpush == None else sum(o[0] for o in lefpush)
	rsum = 0 if rigpush == None else sum(o[0] for o in rigpush)
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







# def _dbgEnter_trimallnonessential(self):
# 	pass
# def _dbgExit_trimallnonessential(self,ahjs):
# 	pass




def _dbgEnter_flatten(self,indesc,mog,assistmog,prep,obj,fillout):
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
def _dbgExit_flatten(self,indesc,mog,assistmog,prep,obj,fillout,ahjs):
	if fillout == None:
		passlen = 0 if prep==None else longcount(prep[0])
		ahjs.setSafety(len(indesc)-passlen)
		# if obj != None and (obj.row!=0 or obj.column!=0):
		# 	for k in ahjs.flat:
		# 		assert k.obj.row!=0 or k.obj.column!=0



def _dbgEnter_verify(self,indesc,carry,reqtype,then,exob):
	# if reqtype: assert not self.verified
	indesc.setSafety(0)
	if carry != None:
		carry.setVerified()
		carry.setSafety(len(indesc))#carry is not slotted for indesc(end) in verify
	self.setSafety(indesc.beginlen())#self is not slotted for indesc(begin) in verify



	if exob != None:
		assert type(exob) is SubsObject
		assert len(exob.subs) != 0
		exob.setVerified()
		exob.setSafety(len(indesc))#exob is not slotted for indesc(end) in verify
def _dbgExit_verify(self,indesc,carry,reqtype,then,exob,outp):

	if reqtype:
		outp,natype = outp
		natype.setSafety(len(indesc))
	elif then:
		outp,ninds = outp
		ninds.setSafety(0)
	outp.setVerified()
	outp.setSafety(len(indesc))

	# if self.row!=0 or self.column!=0: assert outp.row!=0 or outp.column!=0

	# if type(outp) is RefTree and outp.src==None and outp.name!=0:
	# 	assert not indesc.flat[translateBackward(outp.name,indesc.postpushes)].hasobj()





class DDpushError(Exception):
	pass
class DpushError(Exception):
	pass
class PreverifyError(Exception):
	pass



class LanguageError(Exception):
	def __init__(self,pos,message,bassmpt=None):
		super(LanguageError, self).__init__(message + " " + repr(pos))
		self.message = message
		self.bassmpt=bassmpt
		transferlines(self,pos)


class TypeMismatch(Exception):
	def __init__(self,pos,expected,got,context,bassmpt=None):
		super(TypeMismatch, self).__init__("Type mismatch; Expected: "+expected.prepr(FormatterObject(context))+" Got: "+got.prepr(FormatterObject(context))+"   " + repr(pos))
		a = []
		b = []
		expected.pmultiline(a,0,"Expected: ","",FormatterObject(context,forhtml=True))
		got.pmultiline(b,0,"Got: ","",FormatterObject(context,forhtml=True))
		self.expected="<br>".join([j.replace("\t","&nbsp;&nbsp;&nbsp;&nbsp;").replace("<","&lt;").replace(">","&gt;").replace("::lt::","<").replace("::gt::",">") for j in a])
		self.got="<br>".join([j.replace("\t","&nbsp;&nbsp;&nbsp;&nbsp;").replace("<","&lt;").replace(">","&gt;").replace("::lt::","<").replace("::gt::",">") for j in b])

		# self.context = context.reroll().flat if type(context) is ScopeObject else context
		self.bassmpt=bassmpt
		transferlines(self,pos)



class FormatterObject:
	def __init__(self,context,magic=160,forhtml=False):
		self.magic = magic
		self.context = [k.name for k in context.reroll().flat] if type(context) is ScopeObject else context
		self.forhtml = forhtml
	def addbits(self,newbits):
		if self.context==None: return self
		return FormatterObject(self.context+allbits(newbits),magic=self.magic,forhtml=self.forhtml)
	def getname(self,name):
		if type(name) is str: return name
		if self.context == None: return str(name)
		if name>=len(self.context):

			# print(self.context)
			# print(name)
			assert False
		if type(name) is int and name<len(self.context): return self.context[name]
	def red(self,inp):
		if self.forhtml: return "::lt::span style='color:#F92672'::gt::"+inp+"::lt::/span::gt::"
		return inp
	def orange(self,inp):
		if self.forhtml: return "::lt::span style='color:#FD971F'::gt::"+inp+"::lt::/span::gt::"
		return inp




class LazyScopeSeg:
	def __init__(self,core,indesc,mog,assistmog,prep=None,obj=None,fillout=None):
		self.core = core
		self.indesc = indesc
		self.mog = mog
		self.assistmog = assistmog
		self.prep = prep
		self.obj = obj
		self.fillout = fillout
		self.flat = []
		def inner(rec0):
			if type(rec0) is list:
				for y in rec0: inner(y)
			else: self.flat.append(LazyTypeRow(self,len(self.flat),rec0))
		inner(self.mog)




	def setSafety(self,nu):
		pass
	def getSafety(self):
		pass


	def unspool(self):
		res = self.core.flatten(self.indesc,self.mog,self.assistmog,self.prep,None if self.obj == None else self.obj.unspool(),fillout=self.fillout,force=True)
		self.__dict__ = res.__dict__
		self.__class__ = res.__class__
		return self

	def beginlen(self):
		return len(self.flat)
	def __len__(self):
		return len(self.flat)
	def setVerified(self):
		pass
	def setSafetyrow(self,safe):
		pass
	def getSafetyrow(self):
		return None

# class Computation:
# 	def __init__(self,wildin=None,spaces=None,verjson=None):
# 		self.wildin   = {} if wildin == None else wildin
# 		self.spaces   = {} if spaces == None else spaces
# 		self.jsonobjs = [] if verjson == None else verjson
# 	def registerAndExtract(self,add,ver):
# 		self.wildin[add] = len(self.jsonobjs)
# 		space = {}
# 		self.spaces[len(self.jsonobjs)] = space
# 		self.jsonobjs.append(ver.toJSON())
# 		return Computation(self,space,self.spaces,self.jsonobjs)
# 	def register(self,add,ver):
# 		self.wildin[add] = len(self.jsonobjs)
# 		self.jsonobjs.append(ver.toJSON())
# 	def toJSON(self):
# 		return {
# 			"unverstructures":[{"k":list(k),"v":v} for k,v in self.wildin.items()]
# 			"spaces":[{"k":k,"v":[{"k":list(k),"v":v} for k,v in p.items()]} for k,p in self.spaces.items()],
# 			"verstructures":self.jsonobjs
# 		}



# class JSONComputationTransformer:
# 	def main(self,json):
# 		return Computation(
# 			{tuple(a["k"]):a["v"] for a in json["unverstructures"]},
# 			{a["k"]:{tuple(b["k"]):b["v"] for b in a["v"]} for a in json["spaces"]},
# 			json["verstructures"]
# 		)



class ContextYam:
	def __init__(self,operators,dependencies,assumed=None):#,lastComputation
		self.operators = operators
		self.dependencies = dependencies
		self.assumed=assumed#pos,name,chosen,alternatives
		# self.lastComputation = lastComputation
		# self.nextComputation = Computation()
	def setassumed(self,assmus):
		return ContextYam(self.operators,self.dependencies,assmus)



class ScopeObject:
	def __init__(self,flat=None,prpush=None,popush=None,oprows=None):
		self.oprows     = [] if oprows == None else oprows
		self.prepushes  = [] if prpush == None else [k for k in prpush if k[0]!=0]
		self.postpushes = [] if popush == None else [k for k in popush if k[0]!=0]
		self.flat = [] if flat == None else flat
		self.memo = []

		def _dbgTest():
			#make sure there are no switch pushes in self.postpushes.
			assert translateForwardGentle(len(self.flat),self.postpushes) == len(self)
			assert translateForward(len(self.flat),self.postpushes) == len(self)
			assert translateBackward(len(self.flat),self.prepushes) == self.beginlen()
			assert translateForward(self.beginlen(),self.prepushes) == len(self.flat)


	def setassumed(self,assmus):
		return ScopeObject(self.flat,self.prepushes,self.postpushes,self.oprows.setassumed(assmus))

	# def withoutprepush(self):
	# 	return ScopeObject(self.flat,[],self.postpushes,self.oprows)

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
		if len(newflat.flat) == 0: return self
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes+[(-len(newflat.flat),len(self))],self.oprows)
	def sneakadd(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		if len(newflat.flat) == 0: return self
		return ScopeObject(self.flat+newflat.flat,self.prepushes+[(len(newflat.flat),len(self.flat))],self.postpushes,self.oprows)


	def posterase(self,amt):
		if amt == 0: return self
		return ScopeObject(self.flat,self.prepushes,self.postpushes+[(amt-len(self),amt)],self.oprows)
	def preerase(self,amt):
		#examine this more closely...
		if amt == 0: return self
		# return ScopeObject(self.flat,self.prepushes+[(len(self)-amt,self.beginlen()+amt-len(self))],self.postpushes,self.oprows)
		return ScopeObject(self.flat,self.prepushes+[(amt,len(self.flat)-amt)],self.postpushes,self.oprows)
	def sneakinsert(self,nflat,fillout):
		def _dbgEnter():
			self.setSafety(0)
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		if len(nflat.flat) == 0: return self
		npop = copy.copy(self.postpushes)
		cr1=fillout
		for j in range(len(npop)):
			if cr1>=npop[j][1]-npop[j][0]:cr1+=npop[j][0]
			else: npop[j] = (npop[j][0],npop[j][1]+len(nflat.flat))
		cr0=fillout
		return ScopeObject(self.flat[:fillout] + nflat.flat + [k.dpush([(len(nflat.flat),cr1)]) for k in self.flat[fillout:]],self.prepushes+[(len(nflat.flat),cr0)],npop,self.oprows)


	def setSafety(self,safe):
		return
		for i in range(len(self.flat)):
			cr = translateForwardGentle(i,self.postpushes)
			self.flat[i].setVerified()
			try:
				self.flat[i].setSafetyrow(safe+cr)
			except Exception as u:
				print()
				print(self)
				print(i,cr,self.flat[i].getSafetyrow())
				print()

				raise u
			if safe==0 and type(self.flat[i]) is TypeRow and type(self.flat[i].obj) is RefTree and self.flat[i].obj.src==None:

				cr1=translateBackward(self.flat[i].obj.name,self.postpushes)

				assert not self.flat[cr1].hasobj()

	def trimabsolute(self,amt):
		def _dbgEnter():
			self.setSafety(0)
		def _dbgExit(ahjs):
			assert len(self)-amt == len(ahjs)
			assert self.beginlen() == ahjs.beginlen()
		# trimabsolute should expect and eliminate all prepushes leading up to the trimmed data
		coec = translateBackwardPreserve(len(self)-amt,self.prepushes)
		ahjs = ScopeObject(self.flat[:len(self.flat)-amt],coec,self.postpushes,self.oprows)
		return ahjs


	def prepushPR(self,pushes):
		if all(k[0]==0 for k in pushes): return self
		res = ScopeObject(self.flat,pushes+self.prepushes,self.postpushes,self.oprows)
		res.memo = [(pushes+pres,com,res) for pres,com,res in self.memo]
		return res
	def postpushPO(self,pushes):
		if all(k[0]==0 for k in pushes): return self
		res = ScopeObject(self.flat,self.prepushes,self.postpushes+pushes,self.oprows)
		return res


	def beginlen(self):
		return len(self.flat) - sum([l[0] for l in self.prepushes])
	def __len__(self):
		return len(self.flat) + sum([l[0] for l in self.postpushes])
	def reroll(self):
		def _dbgEnter():
			self.setSafety(0)
		def _dbgExit(ahjs):
			ahjs.setSafety(0)

		#be careful with reroll...
		databus = copy.copy(self.flat)
		for j in self.postpushes:
			databus = databus[:j[1]]+databus[j[1]-j[0]:]
		return ScopeObject(databus,[],[],self.oprows)


	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		remapflat = [k.nonsilent() for k in self.flat]
		for row in range(len(remapflat)):
			cr=row
			for j in self.postpushes:
				if cr>=j[1]-j[0]:cr+=j[0]
				elif cr>=j[1]:
					cr=None
					break
			pr=row
			for j in reversed(self.prepushes):
				if pr>=j[1]+j[0]:pr-=j[0]
				elif pr>=j[1]:
					pr=None
					break
			name = "("+remapflat[row].name+")" if remapflat[row].name != None else ""
			remapflat[row].name = ("" if pr == None else str(pr))+"->"+("" if cr == None else str(cr))+name
		pmultilinecsv(out,indent,remapflat,prepend+"[[","]]"+postpend+repr(self.postpushes)+" -- "+repr(self.prepushes),context,callback=callback)



	def symextract(self,name,subs,carry=None,reqtype=False,safety=None,verify=True,limiter=None,pos=None,cosafety=None,preventsub=False):
		def _dbgEnter():
			self.setSafety(0)
			for j in subs:
				assert type(j) is tuple and len(j) == 2
				assert type(j[1]) is tuple and len(j[1]) == 2
				if j[1][1]==False:
					j[1][0].setSafety(self.beginlen())
				else:
					j[1][0].setSafety(len(self))

		for k in subs:
			assert len(k) == 2
			assert len(k[1]) == 2
		def compachelper(assign,row,earlyabort):
			def _dbgExit(ahjs):
				if ahjs != None:
					outp = ahjs
					if reqtype:
						outp,ty = ahjs
						ty.setSafety(len(self))

					# if pos!=None: assert outp.row!=0 or outp.column!=0
					outp.setVerified()
					outp.setSafety(len(self))
			if row == 0:
				return (RefTree(verdepth=len(self),pos=pos),RefTree(verdepth=len(self),pos=pos)) if reqtype else RefTree(verdepth=len(self),pos=pos)
			cr=translateForwardGentle(row,self.postpushes)
			basevalid = canTranslate(row,self.postpushes)
			if preventsub and not basevalid: raise DpushError()

			# self.flat[row].setSafetyrow(cr)

			curr = self.flat[row].unspool().type.dpush([(len(self)-cr,min(cr,len(self)))])

			bedoin = DualSubs(verdepth=len(self))
			cuarg  = DualSubs(verdepth=len(self))
			indesc = self
			wsub = subs
			mood = []
			onehot = 0
			while len(wsub):
				if type(curr.unspool()) is not Strategy:
					if earlyabort: return None
					raise LanguageError(wsub[0][1][0],str(name)+" Recieved too many arguments.")
				se = assign(wsub,curr.args)
				if se == None:
					if earlyabort: return None
					raise LanguageError(wsub[0][1][0],"Incomprehensible argument names.")

				# print(self)
				# print(subs,name," - ",curr.args,se[0])
				# for sos in se[0][0]:
				# 	print(sos[0],sos[1].prepr(context=self),sos[2] if type(sos[2]) is bool else sos[2].prepr(context=self))
				# print(onehot)

				shim = curr.args.peelcompactify(indesc,se[0],then=True,earlyabort=earlyabort)
				if shim == None: return None
				(mprime,earlyabort),indescprime = shim

				mood = se[0][0]#this is a problem...
				onehot+=1

				wsub = [(y[0],(y[1][0].dpush([(len(indescprime)-len(indesc),len(indesc))]) if y[1][1]!=False else y[1][0],y[1][1] if type(y[1][1]) is bool else y[1][1].dpush([(len(indescprime)-len(indesc),len(indesc))]))) for y in se[1]]
				bedoin = bedoin + curr.args
				indesc = indescprime
				cuarg = cuarg+mprime

				curr = curr.type

			oldcurr = curr

			cold = preventsub or self.flat[row].obj != None

			if verify or reqtype:
				curr = oldcurr.verify(indesc.reroll(),RefTree(verdepth=len(indesc))).addfibration(cuarg)
				if verify: assertstatequal(self,pos,carry,curr)

			if len(bedoin)==0:
				if basevalid: obj = RefTree(name=cr,verdepth=len(self),pos=pos,cold=cold)
				if self.flat[row].obj != None and not preventsub:
					obj = self.flat[row].obj.dpush([(len(self)-cr,min(cr,len(self)))],force=True).addalts([obj] if basevalid else [])
				return (obj,curr) if reqtype else obj

			simpl = []
			camax = len(cuarg.rows)
			while camax>0 and (cuarg.rows[camax-1].obj==None)==(bedoin.rows[camax-1].obj==None): camax -= 1
			for h in range(camax):
				if bedoin.rows[h].obj==None:
					for k in mood:
						if k[0]==[h] and onehot<2:
							simpl.append(SubRow(None,k[1]))
							break
					else:
						# raise LanguageError(subs[0][1][0],"Hole in arguments list...")
						nocue = oldcurr.addfibration(bedoin).dpush([(len(indesc)-len(self),len(self))],force=True)
						drargs = bedoin.emptyinst(len(self)).verify(indesc.reroll(),nocue.args.unspool().nonsilent(),force=True)
						print("\n=0=0=0=0=0=0=0===0=00=0=0==00=0=00=00=0")
						print(mood)
						print(cuarg)
						print(bedoin)
						print(nocue)
						print(drargs)

						if basevalid: obj = RefTree(cr,drargs,verdepth=len(indesc),pos=pos,cold=cold)
						if self.flat[row].obj != None and not preventsub:
							obj = self.flat[row].obj.dpush([(len(self)-cr,min(cr,len(self)))]).verify(indesc.reroll().preerase(len(indesc)-len(self)),nocue,exob=drargs if len(drargs.subs)>0 else None).addalts([obj] if basevalid else [])
						obj = obj.addlambdas(cuarg)
						return (obj,curr) if reqtype else obj

			drargs = SubsObject(simpl,verdepth=len(self))
			if basevalid: obj = RefTree(cr,drargs,verdepth=len(self),pos=pos,cold=cold)
			if self.flat[row].obj != None and not preventsub:
				# drargs = drargs.dpush([(len(indesc)-len(self),len(self))],force=True)
				nocue = oldcurr.addfibration(bedoin)#.dpush([(len(indesc)-len(self),len(self))],force=True)#indesc.reroll().preerase(len(indesc)-len(self))



				obj = self.flat[row].obj.dpush([(len(self)-cr,min(cr,len(self)))]).verify(self.reroll(),nocue,exob=drargs if len(drargs.subs)>0 else None).addalts([obj] if basevalid else [])
			# obj = obj.addlambdas(cuarg)

			return (obj,curr) if reqtype else obj



		class Scontrol:
			def __init__(self,safety):
				self.safety = safety
			def __call__(self,ksubs,args):
				oflow = []
				snj = args.compacassign(ksubs,oflow,cosafety,self.safety)
				if snj==None: return None
				self.safety = None
				return (snj,oflow)
		def momo(ksubs,args):
			souts = []
			for k in range(len(args)):
				if k>=len(ksubs):break
				if args.rows[k].obj == None:
					souts.append(([k],ksubs[k][1][0],ksubs[k][1][1]))
			return ((souts,True),ksubs[len(souts):])
		if len(self.flat) == 0 or name == 0 and limiter==None:
			return (RefTree(verdepth=len(self)),RefTree(verdepth=len(self))) if reqtype else RefTree(verdepth=len(self))
		if type(name) is int:
			return compachelper(momo,translateForward(name,self.prepushes) if limiter==None else name+limiter,False)
		else:
			potentialmatches = 0
			for row in reversed(range(len(self.flat))):
				if limiter!= None and row<limiter: break
				if self.flat[row].name != name: continue
				if limiter== None and not canTranslateBackward(row,self.prepushes): continue
				potentialmatches+=1
			for row in reversed(range(len(self.flat))):
				if limiter!= None and row<limiter: break
				if self.flat[row].name != name: continue
				if limiter== None and not canTranslateBackward(row,self.prepushes): continue
				spa = compachelper(Scontrol(safety),row,potentialmatches!=1)
				if spa != None: return spa


	def precidence(self,ind):
		for j in range(len(self.oprows.operators)):
			if ind in self.oprows.operators[j][0]:
				return (j,self.oprows.operators[j][1]['associate'])
	def __repr__(self):
		# hu = copy.copy(self.postpushes)
		# y = 0
		output = []
		for d in self.flat:
			output.append((d.name if type(d.name) is str else repr(d.name))+("|" if d.hasobj() else ""))
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



	def concatenate(self,other):
		def _dbgEnter():
			self.setSafety(0)
			other.setSafety(0)
			assert len(self) == other.beginlen()
		def _dbgExit(ahjs):
			assert ahjs.beginlen() == self.beginlen()
			assert len(ahjs) == len(other)
			ahjs.setSafety(0)

		assert False#need an assert here to make sure switch pushes aren't contained in other.prepush.

		for pres,com,res in self.memo:
			if other.prepushes == com.prepushes and len(other.flat)>=len(com.flat) and len(other.postpushes)>=len(com.postpushes):
				if all(other.flat[a] is com.flat[a] for a in range(len(com.flat))) and other.postpushes[:len(com.postpushes)] == com.postpushes:
					return res.prepushPR(pres).addflat(ScopeObject(other.flat[len(com.flat):])).postpushPO(other.postpushes[len(com.postpushes):])
		
		purepostpushes = [k for k in self.postpushes if k[0]<0]

		modo = copy.copy(other.flat)
		gorsh = copy.copy(purepostpushes+other.prepushes)
		norsh = []
		seethe = copy.copy(self.prepushes)
		something = []
		for i in reversed(range(len(gorsh))):
			if gorsh[i][0]<0:
				amt,lim = gorsh.pop(i);
				for j in range(i,len(gorsh)):
					if gorsh[j][1]>=lim: gorsh[j]=(gorsh[j][0],gorsh[j][1]-amt)
					else: lim+=gorsh[j][0]
				norsh.insert(0,(amt,lim))
		
		for k in range(len(purepostpushes)):
			assert norsh[k][0] == purepostpushes[k][0]

		for i in reversed(range(len(norsh))):
			j = norsh[i][1]
			while j < norsh[i][1]-norsh[i][0]:
				if j>len(modo):
					print("alright")
					print(modo)
					print(j)
					print(self)
					print(other)
					assert False
				lidex = translateBackward(j,norsh[:i])#are you sure about
				safedex = lidex
				for k in reversed(range(-len(seethe),len(gorsh))):
					if k>=0: amt,lim = gorsh[k]
					else:    amt,lim = seethe[k]
					if lidex>=max(lim+amt,lim):
						lidex-=amt
					elif lidex>=lim: # maybe delete gorsh...
						if k>=0:
							gorsh[k] = (gorsh[k][0]-1,gorsh[k][1])
						else:
							something.append(safedex)
							seethe[k] = (seethe[k][0]-1,seethe[k][1])

						norsh[i] = (norsh[i][0]+1,norsh[i][1])           
						if i<len(purepostpushes): purepostpushes[i] = (purepostpushes[i][0]+1,purepostpushes[i][1])
						lidex = j
						for s in reversed(range(i)):
							if lidex>=norsh[s][1]: lidex-=norsh[s][0]
							else:
								norsh[s] = (norsh[s][0],norsh[s][1]-1)
								if s<len(purepostpushes): purepostpushes[s] = (purepostpushes[s][0],purepostpushes[s][1]-1)
						for s in reversed(range(k+1,len(gorsh))):
							if s>=0:
								if lidex>=gorsh[s][1]: lidex-=gorsh[s][0]
								else: gorsh[s] = (gorsh[s][0],gorsh[s][1]-1)
							else:
								if lidex>=seethe[s][1]: lidex-=seethe[s][0]
								else: seethe[s] = (seethe[s][0],seethe[s][1]-1)
						break
					if k==0: safedex=lidex
				else:
					lidex=safedex
					for thing in something:
						if safedex>=thing: lidex+=1

					acet = [(-a,l) for a,l in reversed(translateForwardGentlePreserve(safedex,purepostpushes))]
					acet += translateForwardPreserve(safedex,gorsh+norsh[:i])
					bocet = translateForwardGentlePreserve(j,norsh[i:]+other.postpushes)

					# translateBackward(j,norsh[:i])

					# <----- this doesnt always apply


					jins = ScopeObject(modo[:j],acet,bocet,self.oprows)


					cufn = self.flat[lidex].vershortcut(jins)
					modo.insert(j,cufn)
					j+=1
		res = ScopeObject(modo,seethe+gorsh,norsh+other.postpushes,self.oprows)
		self.memo.append(([],other,res))

		return res



class LazyTypeRow:
	def __init__(self,ref,num,name,indesc=None,expushes=None):
		self.ref = ref
		self.num = num
		self.name = name
		self.indescs = [] if indesc==None else indesc
		self.expushes = [] if expushes==None else expushes
	def unspool(self):
		if type(self.ref) is LazyScopeSeg: self.ref.unspool()
		res = self.ref.flat[self.num].unspool()
		if self.indescs!=[]: res = res.vershortcut(singularindesc(self.indescs))
		if self.expushes!=[]: res = res.dpush(self.expushes)
		self.__dict__ = res.__dict__
		self.__class__ = res.__class__
		return self
	def vershortcut(self,indesc):
		return LazyTypeRow(self.ref,self.num,self.name,self.indescs+[indesc],self.expushes)
	def dpush(self,pushes):
		return LazyTypeRow(self.ref,self.num,self.name,self.indescs,self.expushes+pushes)


	def hasobj(self):
		if type(self.ref) is ScopeObject: return self.unspool().obj!=None
		return self.ref.obj != None

	def setSafetyrow(self,nu):
		pass
	def getSafetyrow(self):
		pass
	def setVerified(self):
		pass

#have each scope contain a reference to the original that created it that you iterate backwards over like a linked list to find the thing you did the operation on...
#then just compare indecies between the two to figure out the data you need to add.

#not sure i like that... it keeps references alive when they don't need to be. it seems better if you just heavy compare...

class TypeRow:
	def setVerified(self):
		self.type.setVerified()
		if self.obj != None: self.obj.setVerified()
	def setSafetyrow(self,safe):
		if self.type != None: self.type.setSafety(safe)
		if self.obj != None: self.obj.setSafety(safe)
	def getSafetyrow(self):
		res = self.type.getSafety()
		if self.obj != None:
			if res == None:
				res = self.obj.getSafety()
				self.type.setSafety(res)
			else: self.obj.setSafety(res)
		return res
	def nonsilent(self):
		return TypeRow(self.name,self.type,self.obj,{'silent':False,'contractible':False})
	def __init__(self,name,ty,obj=None,silent=None):
		self.name = name
		self.type = ty
		self.obj  = obj
		self.silent = silent
		if type(ty) is Lambda or type(ty) is SubsObject: assert False
		assert self.type != None or self.obj != None
		assert type(self.type) is not Strategy or self.type.type != None or self.obj != None


	# pjson  -> touches,PJID
	# (PJID) -> [verified]


	# pJSONout -> (adds to jain and returns int? nah)


	# - before verifying, recursively assign PJIDs for anything with a match.

	# - verifying an unverified structure twice kills the program
	# - verifying an unverified structure that has a PJID already will search jain for a match to skip some computation.
	# - verifying an unverified structure assigns it a PJID in jainprime

	# ->>>>>>>>> verifying a file reference should also compare an md5 to make sure it didnt change.


	# - from json should also accept a DPUSH variable-> always applies to all.




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
			"cent":self.type.unspool().toJSON(),
			"obj":None if self.obj==None else self.obj.unspool().toJSON(),
			"silent":self.silent
		}

	def ddpush(self,amt,lim,repls=None,replsrc=None):
		return TypeRow(self.name,self.type.ddpush(amt,lim,repls,replsrc),None if self.obj == None else self.obj.ddpush(amt,lim,repls,replsrc),self.silent)
	def detect(self,ranges):
		return self.type.quickdetect(ranges) or self.obj!=None and self.obj.quickdetect(ranges)

	def dpush(self,pushes):
		return TypeRow(self.name,self.type.dpush(pushes),None if self.obj == None else self.obj.dpush(pushes),self.silent)



	def hasobj(self):
		return self.obj != None

	def vershortcut(self,indesc):
		return TypeRow(self.name,self.type.verify(indesc),None if self.obj == None else self.obj.verify(indesc),self.silent)
	def unspool(self):
		return self

	def prepr(self,context):
		res = "" if self.name == None else pmultilinelist(self.name,context)+":"
		if self.silent!=None and self.silent["silent"]:
			if res=="": res = "?:"
			else: res = res[:-1]+"?:"
		if self.type != None: res = res+self.type.prepr(context)
		if self.obj != None: res = res+" = "+self.obj.prepr(context)
		return res
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		def calls(out,prepend,context_):
			if self.obj != None:
				self.obj.pmultiline(out,indent,prepend,postpend,context,callback=callback)
			else:
				if callback == None:
					out.append("\t"*indent+prepend+postpend)
				else:
					callback(out,prepend+postpend,context)
		name = "" if self.name == None else pmultilinelist(self.name,context)+":"
		self.type.pmultiline(out,indent,prepend+name," = " if self.obj != None else "",context,calls)
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
		return self.obj.unspool().toJSON()

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
		res = "" if self.name == None or context!=None else pmultilinelist(self.name,context)+" = "
		res = res+self.obj.prepr(context)
		return res
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		name = "" if self.name == None else pmultilinelist(self.name,context)+" = "
		self.obj.pmultiline(out,indent,prepend+name,postpend,context,callback)
	def __repr__(self):

		return self.prepr(FormatterObject(None))



# 8 9


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
			if not canTranslate(touch,ranges): return self.detect(ranges)
		return False

	def fibrationalt(self,args):
		vers = []
		for ver in self.altversion:
			try: vers.append(ver.addfibration(args))
			except DpushError: vers = vers + ver.fibrationalt(args)
		return vers

	def lambdaalt(self,args,si=None):
		vers = []
		for ver in self.altversion:
			try: vers.append(ver.addlambdas(args,si))
			except DpushError: vers = vers + ver.lambdaalt(args,si)
		return vers


	def ddpushalt(self,amt,lim,repls,replsrc):
		vers = []
		for ver in self.altversion:
			try: vers.append(ver.ddpush(amt,lim,repls=repls,replsrc=replsrc))
			except DDpushError: vers = vers + ver.ddpushalt(amt,lim,repls,replsrc)
		return vers
	def dpushalt(self,pushes):
		vers = []
		for ver in self.altversion:
			if ver.detect(pushes): vers = vers+ver.dpushalt(pushes)
			else: vers.append(ver.dpush(pushes))
		return vers
	def verifyalt(self,indesc,carry,exob):
		vers = []
		for ver in self.altversion:
			if ver.detect(indesc.prepushes): vers = vers+ver.verifyalt(indesc,carry,exob)
			else:
				try: vers.append(ver.verify(indesc,carry,exob=exob))
				except DpushError: vers = vers+ver.verifyalt(indesc,carry,exob)
		return vers
	def addalts(self,alts):
		if not len(alts):return self
		cop = copy.copy(self)
		for alt in alts:
			alt.setSafety(self.getSafety())
		cop.altversion = cop.altversion + alts
		for alt in alts:
			assert type(alt) is RefTree and alt.src==None#safemode
			cop.touches.update(alt.args.touches)
		return cop


	def flatten(self,indesc,mog,assistmog=None,prep=None,obj=None,fillout=None,force=False):

		if type(mog) is list: raise LanguageError(self,"invalid renamer pattern.")
		if prep != None: njprep = prep[0].unspool().dpush([(len(indesc)-longcount(prep[0])-prep[1],prep[1])],force=True)
		if prep == None or len(njprep.rows)==0:
			return ScopeObject([TypeRow(mog,self.verify(indesc),None if obj == None else obj)])
		else:
			spap = len(indesc)-longcount(njprep)

			t1 = self.verify(indesc).addfibration(njprep)

			t2 = None if obj == None else obj.addlambdas(njprep)

			return ScopeObject([TypeRow(mog,t1,t2)])
	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not int: raise LanguageError(self,"invalid renamer pattern.")
		prep = None if prep == None else prep[0].dpush([(limit-prep[1],prep[1])])

		return RefTree(name=mog,args=prep,verdepth=limit)
	def addfibration(self,args):
		shaz = longcount(args)
		if len(args) == 0:
			return self.dpush([(-shaz,self.verdepth-shaz)])
		return Strategy(args,self,verdepth=self.verdepth-shaz,pos=self,altversion=self.fibrationalt(args))
	def addlambdas(self,args,si=None):
		starter = self.verdepth-longcount(args)
		si = args.semavail() if si==None else si
		disgrace = []
		largs = args.trimallnonessential(si,disgrace=disgrace)
		outp = self.dpush(disgrace) if len(disgrace) else self
		elim=0
		fafter = starter+longcount(largs)
		if type(outp) is RefTree and outp.name<starter:
			elim=0
			while elim<len(largs.rows) and elim<len(outp.args.subs):
				ndepth = starter+longcount(si[:len(si)-elim-1])
				purecomponent = largs.rows[len(largs.rows)-1-elim].type.emptyinst(fafter,striphuman(ndepth,si[len(si)-1-elim])[0])
				if not outp.args.subs[len(outp.args.subs)-1-elim].obj.compare(purecomponent): break
				elim+=1
			if elim:
				ndepth = starter+longcount(si[:len(si)-elim])
				nsubs = SubsObject([k.dpush([(ndepth-fafter,ndepth)]) for k in outp.args.subs[:len(outp.args.subs)-elim]],verdepth=ndepth)
				outp = RefTree(outp.name,nsubs,verdepth=ndepth,cold=outp.cold)
		if type(outp) is Lambda:
			return Lambda(si[:len(si)-elim]+outp.si,outp.obj,pos=self,verdepth=starter,altversion=self.lambdaalt(args,si))
		if len(si)==elim: return outp.addalts(self.lambdaalt(args,si))
		return Lambda(si[:len(si)-elim],outp,pos=self,verdepth=starter,altversion=self.lambdaalt(args,si))



	def unspool(self):
		return self
		pass
	def __repr__(self):
		return self.prepr(FormatterObject(None))

def altPmultiline(F):
	def wrapper(self,out,*args,**kwargs):
		if len(self.altversion):
			complete = []
			for a in self.altversion:
				complete.append([])
				a.pmultiline(complete[-1],*args,**kwargs)
			m = complete[0]
			for a in complete[1:]:
				if sum(len(b) for b in a)<sum(len(b) for b in m): m = a
			for j in m: out.append(j)
		else:
			F(self,out,*args,**kwargs)
	return wrapper


def altPrepr(F):
	def wrapper(self,*args,**kwargs):
		if len(self.altversion):
			complete = [a.prepr(*args,**kwargs) for a in self.altversion]
			m = complete[0]
			for a in complete[1:]:
				if len(a)<len(m): m = a
			return m
		return F(self,*args,**kwargs)

	return wrapper

def conditionalverify(F):
	def wrapper(self,indesc,carry=None,reqtype=False,then=False,exob=None,force=False,**kwargs):
		def _dbgEnter():
			if exob!=None: exob.setSafety(len(indesc))
		"""dbg_ignore"""
		if not self.verified or (exob!=None and type(self) is not RefTree) or reqtype or then or any(len(indesc.flat) and indesc.flat[translateForward(i,indesc.prepushes)].hasobj() for i in self.touches):
			return F(self,indesc,carry,reqtype,then,exob,force,**kwargs)
		# print(self,self.touches)
		# m = min(self.touches)
		# pushes = translateForwardPreserve(m,indesc.prepushes)+translateForwardPreserve(translateForward(m,indesc.prepushes),indesc.postpushes)
		# if len(pushes):
		# 	return self.dpush(pushes)


		if len(indesc.prepushes) or len(indesc.postpushes):
			self = self.dpush(indesc.prepushes+indesc.postpushes,force=force)

		if exob!=None:
			self = RefTree(self.name,SubsObject(self.args.subs+exob.subs,verdepth=self.verdepth),self.src,verdepth=self.verdepth,pos=self,cold=self.cold).addalts(self.verifyalt(indesc,carry,exob))

		return self
		# return self
	return wrapper


def tsSetDpush(s,pushes):
	return {translateForward(t,pushes) for t in s}

def tsSetIndesc(s,indesc):
	k = set()
	for t in s:
		l = translateForward(t,indesc.prepushes)
		if indesc.flat[l].hasobj():
			k.update(indesc.flat[l].unspool().obj.touches)
		else:
			k.add(translateForward(l,indesc.postpushes))
	return k



class LazyEvaluation:
	def __init__(self,core,JGIVT,indesc=None,carry=None,postpush=None,exob=None):
		self.core = core
		self.indescs = [] if indesc==None else indesc
		self.carry = carry
		self.exob = exob
		self.verified = True
		self.postpushes = [] if postpush == None else postpush
		if type(core) is LazyEvaluation: assert False
		self.complexity = 1#<><> think about this
		if self.indescs != []:
			self.core.setSafety(self.indescs[0].beginlen())
			for h in self.indescs:
				h.setSafety(0)

		self.touches = JGIVT

	# def toJSON(self):
	# 	return {
	# 		"type":"LazyEvaluation",
	# 		"layers":[k.toJSON() for k in self.rows],
	# 		"postpush":
	# 	}

	def emptyinst(self,limit,mog=False,prep=None):
		return self.unspool().emptyinst(limit,mog,prep)


	def caneasy(self):
		return self.core.caneasy() 

	def needscarry(self):
		return True

	def addfibration(self,args):
		return self.unspool().addfibration(args)
	def addlambdas(self,args,si=None):
		return self.unspool().addlambdas(args,si)

	# def fulavail(self):
	# 	if type(self.core) is DualSubs or type(self.core) is Strategy: return self.core.fulavail()

	
	def flatten(self,indesc,mog=False,assistmog=None,prep=None,obj=None,fillout=None,force=False):

		assert False#if self.postpushes contains a switch push, you gotta set force to true, and maybe do two separate passes

		if mog==False:
			# if type(self.core) is Strategy or type(self.core) is DualSubs:

			# 	sel = self if type(self) is DualSubs else self.type if type(self) is Strategy else None
			# 	if trim: mog = untrim(sel.unspool(),mog)
			# 	if mog == False: mog = sel.fulavail()



			# else:
			return self.unspool().flatten(indesc,mog,assistmog,prep,obj,fillout,trim,force=force)#whocares this part is very specific

		if not force: return LazyScopeSeg(self,indesc,mog,assistmog,prep,obj,fillout)

		if fillout != None: return self.unspool().flatten(indesc,mog,assistmog,prep,obj,fillout,trim,force=True)





		jins = singularindesc(self.indescs+[indesc.prepushPR(self.postpushes)])




		if type(self.core) is Strategy or type(self.core) is DualSubs:
			return self.core.flatten(jins,mog,assistmog,prep,obj,fillout,trim,force=True)

		moto = self.core.verify(jins,RefTree(verdepth=len(jins)),force=True)
		if type(moto) is Strategy or type(moto) is DualSubs:
			return moto.flatten(indesc.reroll(),mog,assistmog,prep,obj,fillout,trim,force=True)



		assert not trim
		if type(mog) is list: raise LanguageError(moto,"invalid renamer pattern.")
		if prep != None: njprep = prep[0].unspool().dpush([(len(indesc)-longcount(prep[0])-prep[1],prep[1])],force=True)
		if prep == None or len(njprep.rows)==0:
			return ScopeObject([TypeRow(mog,moto,None if obj == None else obj)])
		else:
			spap = len(indesc)-longcount(njprep)

			t1 = moto.addfibration(njprep)

			t2 = None if obj == None else obj.addlambdas(njprep)

			return ScopeObject([TypeRow(mog,t1,t2)])


	def setSafety(self,safe):
		if self.indescs == []:
			self.core.setSafety(safe-sum(k[0] for k in self.postpushes))
		else:
			assert self.getSafety() == safe
	def getSafety(self):
		mode = self.core.getSafety()
		if self.indescs != []:
			self.core.setSafety(self.indescs[0].beginlen())
			mode = len(self.indescs[-1])
		if mode != None: mode += sum(k[0] for k in self.postpushes)
		return mode

	def __repr__(self):
		return self.prepr(FormatterObject(None))
	@altPrepr
	def prepr(self,context):
		assert False#unimplemented.
		if self.indescs == []: return "|+"+str(sum(k[0] for k in self.postpushes))+"|"+self.core.prepr(context)
		return context.orange("|")+str(self.indescs[0].beginlen())+"->"+str(len(self.indescs[-1]))+"+"+str(sum(k[0] for k in self.postpushes))+"|"+self.core.prepr(context)
	@altPmultiline
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		assert False#unimplemented.
		if self.indescs == []: return self.core.pmultiline(out,indent,prepend+"|+"+str(sum(k[0] for k in self.postpushes))+"|",postpend,context,callback)
		return self.core.pmultiline(out,indent,prepend+"|"+str(self.indescs[0].beginlen())+"->"+str(len(self.indescs[-1]))+"+"+str(sum(k[0] for k in self.postpushes))+"|",postpend,context,callback)


	def setVerified(self):
		pass
		pass
	def ddpush(self,amt,lim,repls=None,replsrc=None):
		return self.unspool().ddpush(amt,lim,repls,replsrc)
	def detect(self,ranges):

		assert False
		# return self.obj.detect(ranges)

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		return self.unspool().compare(other,odsc,thot,extract,lefpush,rigpush)
	def dpush(self,pushes,force=False):
		res = LazyEvaluation(self.core,tsSetDpush(self.touches,pushes),self.indescs,self.carry,self.postpushes+[k for k in pushes if k[0]!=0],self.exob)
		if force: return res.unspool()
		return res
	@conditionalverify
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None,force=False):
		assert not reqtype
		if then: return self.unspool().verify(indesc,carry,reqtype,then,exob)

		if self.exob == None: bex = exob
		elif exob == None: bex = self.exob.verify(indesc,carry,force=True)
		else:
			bex = SubsObject(self.exob.verify(indesc,carry,force=True).subs+exob.subs,verdepth=len(indesc))

		assert False#if postpushes contains a switch push, you gotta set force to true, and maybe do two separate steps.

		jins = self.indescs + [indesc.prepushPR(self.postpushes)]
		res = LazyEvaluation(self.core,tsSetIndesc(self.touches,indesc),jins,carry,[],bex)
		if force: return res.unspool()
		return res

	def unspool(self):
		better = self.core
		if self.indescs != []:
			better = better.verify(singularindesc(self.indescs),self.carry,exob=self.exob,force=True)
		if len(self.postpushes)>0:
			better = better.dpush(self.postpushes,force=True)

		better.setSafety(self.getSafety())


		self.__dict__ = better.__dict__
		self.__class__ = better.__class__
		assert type(self) is not LazyEvaluation
		return self



def initTobj(F):
	def wrapper(self,*args,pos=None,verified=True,altversion=None,**kwargs):
		"""dbg_ignore"""
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
		# else:
		# 	assert self.row!=0 or self.column!=0

	return wrapper

def lazyverify(F):
	@conditionalverify
	def wrapper(self,indesc,carry=None,reqtype=False,then=False,exob=None,force=False,**kwargs):
		"""dbg_ignore"""
		force=True#dbgdbg

		if self.verified and not then and not force and not reqtype and self.complexity> 2:
			return LazyEvaluation(self,tsSetIndesc(self.touches,indesc),[indesc],carry,None,exob)
		return F(self,indesc,carry,reqtype,then,exob,**kwargs)
	return wrapper

def lazydpush(F):
	def wrapper(self,pushes,force=False,**kwargs):
		"""dbg_ignore"""
		force=True#dbgdbg


		if all(k[0]==0 for k in pushes): return self
		if not force and self.complexity> 2:
			return LazyEvaluation(self,tsSetDpush(self.touches,pushes),None,None,pushes,None)
		return F(self,pushes,**kwargs)
	return wrapper


def lazyflatten(F):
	def wrapper(self,indesc,mog=False,assistmog=None,prep=None,obj=None,fillout=None,force=False):
		"""dbg_ignore"""
		force=True#dbgdbg

		# assert False

		sel = self if type(self) is DualSubs else self.type if type(self) is Strategy else None
		if mog == False: mog = sel.fulavail()
		# pamt = None
		if assistmog == None:
			assistmog,ext = striphuman(len(indesc),mog)
			fillout = len(indesc.flat)
		if type(mog) is not list: return Tobj.flatten(self,indesc,mog,assistmog,prep,obj,fillout=fillout)
		if len(sel.fulavail()) != len(mog):
			print(sel)
			print(mog)
			raise LanguageError(self,"wrong number of labels for flattening.")
		if force:
			return F(self,indesc,mog,assistmog,prep,obj,fillout)
		else:
			return LazyScopeSeg(self,indesc,mog,assistmog,prep,obj,fillout)
	return wrapper




# each time you construct a Tobj...




	# alternates are always sorted by root index
	#when comparing, alternates compare only to alternates and following sorted order, and if that fails, the object itself is compared separately.

	# verify should preserve alternates. (and set verified flag)

	# compare should respect alternates.

	# alternates are always reftrees. (keep them unspooled and kill them if they are dpushed out of existence.)

	# maintain alternates under verify and dpush and etc etc. (ddpush?)

#lazyeval should work without alternates.



# could probably use comparison decorator for alternates.




class DualSubs(Tobj):
	@initTobj
	def __init__(self,rows=None,verdepth=None):
		self.rows = rows if rows != None else []
		if verdepth!=None:
			self.verdepth = verdepth
			self.touches = set()
			self.complexity = 1
			for sub in self.rows:
				assert type(sub) is TypeRow#safemode
				self.touches.update(sub.type.touches)
				self.complexity+=sub.type.complexity
				if sub.obj!=None:
					self.touches.update(sub.obj.touches)
					self.complexity+=sub.obj.complexity
			self.touches = {k for k in self.touches if k<verdepth}

	# def preverify(self,OIP):
	# 	allowed references only builds


	# 	if OIP!=None and <><><><><><><>><><><><>><<>><><><><><><>

	# 	btc = Set()
	# 	for a in range(len(self.rows)):
	# 		# if row.name == "*****": raise PreverifyError()
	# 		# if a out of range: process all remaining z
	# 		mtc = Set()
	# 		if type(row.type) is Strategy and row.type.type == None:
	# 			moum = row.type.args.preverify(OIP)
	# 			mtc.update(moum[0])
	# 			if row.obj!=None: mtc.update(row.obj.preverify(moum[1])[0])
	# 		else:
	# 			if row.type!=None: mtc.update(row.type.preverify(OIP)[0])
	# 			if row.obj!=None: mtc.update(row.obj.preverify(OIP)[0])

	# 		if (row.obj==None or row.obj.PJID != None) and (row.type==None or row.type.PJID != None):
	# 			oooooooo

	# 			iterate through new rows-> gather up illegal; offset...





	# 			offset,illegal,precompute = OIP
	# 			if any(a in mtc for a in illegal): return (mtc,None)<><>
	# 			row = row.primToJSON()<--- search onwards for match.



	# 			wild = precompute.wildin.get()
	# 			if wild == None: return (mtc,None)




	# 		row.PJID = wild[0]
	# 		return (mtc,wild[1])
	# 	self.PJID = None
	# 	mtc = Set()
	# 	for row in self.rows:
	# 		if row.name == "*****": raise PreverifyError()#call preverify upon resolution.
	# 		moum = row.preverify(offset,illegal,precompute)
	# 		mtc.update(moum[0])
	# 		if moum[1]==None:
	# 			asdfjk;lasdfjkl;asdfjkl;asjdfkl;ajsdkfl;asdfjkl;asdfjkl;

	# 		else:
	# 			precompute = moum[1]

	# 	for row in self.rows:
	# 		if row.PJID == None:
	# 			return (mtc,precompute)
	# 	wild = precompute.wildin.get(self.primToJSON())
	# 	if wild == None: return (mtc,precompute)
	# 	self.PJID = wild[0]
	# 	return (mtc,precompute)

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
			yud.append(k.prepr(context))
			context = context.addbits(k.name)
		return context.red("{")+",".join(yud)+context.red("}")
	@altPmultiline
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		pmultilinecsv(out,indent,self.rows,prepend+context.red("{"),context.red("}")+postpend,context,lamadapt=lambda x:x.name,callback=callback,delim=context.red(","))
	def nonsilent(self):
		return DualSubs([k.nonsilent() for k in self.rows],pos=self,verdepth=self.verdepth)
	def ddpush(self,amt,lim,repls=None,replsrc=None,disgrace=None):
		disgrace = [] if disgrace == None else disgrace
		left = 0
		cu = []
		for k in range(len(self.rows)):
			try:
				m = self.rows[k]
				if len(disgrace): m = m.dpush(disgrace)
				m = m.ddpush(amt,lim,repls,replsrc)
			except DDpushError as u:
				if self.rows[k].obj == None: raise u
				disgrace.append((-longcount(self.rows[k].name),self.verdepth+left))
			else:
				cu.append(m)
				left += longcount(self.rows[k].name)
		return DualSubs(cu,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc))
	def detect(self,ranges,merge=False):
		if not merge: ranges = copy.copy(ranges)
		dsc = self.verdepth
		for row in self.rows:
			lc = longcount(row.name)
			if row.detect(ranges):
				if row.obj==None: return True
				ranges.append((-lc,dsc))
			else:
				dsc+=lc
		return False
	@lazydpush
	def dpush(self,pushes,disgrace=None):
		# return DualSubs([i.dpush(pushes) for i in self.rows],pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes),altversion=self.dpushalt(pushes))
		disgrace = [] if disgrace == None else disgrace
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
		return DualSubs(cu,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes),altversion=self.dpushalt(pushes))
	def caneasy(self):
		return True
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None,keepr=False,advanced=None):
		if type(other.unspool()) is not DualSubs: return False
		if len(self) == len(other): advanced = None
		if len(self) < len(other) and advanced==None: return False
		if len(self) > len(other): return False
		if lefpush == None: lefpush = []
		if rigpush == None: rigpush = []
		if not keepr:
			lefpush = copy.copy(lefpush)
			rigpush = copy.copy(rigpush)
		lk = 0
		rk = 0
		dsc = self.verdepth + sum(a[0] for a in lefpush)
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
		disgrace = [] if disgrace == None else disgrace

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
				if len(disgrace): m = m.dpush(disgrace)
				if s<len(si) and type(si[s]) is list:
					if type(m.type) is DualSubs:
						left = unshift(left,m.type.rows,self.rows[k].name,si[s])
						m = TypeRow(m.name,m.type.trimallnonessential(si[s]),m.obj,m.silent)
					elif type(m.type) is Strategy and type(m.type.type) is DualSubs:
						left = unshift(left,m.type.type.rows,self.rows[k].name,si[s])
						m = TypeRow(m.name,Strategy(m.type.args,m.type.type.trimallnonessential(si[s]),verdepth=m.type.verdepth),m.obj,m.silent)
					else: raise LanguageError(self,"Invalid split pattern.")
				else:
					left += longcount(self.rows[k].name)
				cu.append(m)
				s += 1
			else:
				disgrace.append((-longcount(self.rows[k].name),self.verdepth+left))
		return DualSubs(cu,verdepth=self.verdepth)
	@lazyflatten
	def flatten(self,indesc,mog,assistmog,prep=None,obj=None,fillout=None):

		s = 0
		lenold = len(indesc)
		cu = ScopeObject()

		for n in range(len(self.rows)):
			nobj = None
			if self.rows[n].obj != None:
				nobj = self.rows[n].obj.verify(indesc)
			else:
				if obj == None: pass
				elif type(obj) is SubsObject: nobj = obj.subs[s].obj.dpush([(len(indesc)-lenold,lenold)])
				elif type(obj) is Lambda and type(obj.obj) is SubsObject: nobj = Lambda(obj.si,obj.obj.subs[s].dpush([(len(indesc)-lenold,lenold)]),obj.pos,verdepth=len(indesc),pos=obj)
				else: nobj = RefTree(src=obj.dpush([(len(indesc)-lenold,lenold)]),name=s,verdepth=len(indesc),pos=obj)
				s+=1
			nflat = self.rows[n].type.flatten(indesc,mog[n],assistmog[n],prep,obj=nobj,fillout=fillout)
			cu.flat += nflat.flat
			if conservativeeq(self.rows[n].name,mog[n]) and prep == None:
				indesc = indesc.addflat(nflat)
			else:
				indesc1 = indesc.sneakinsert(nflat,fillout)
				passprep = (prep[0].emptyinst(len(indesc1),striphuman(len(indesc1)-longcount(prep[0]),prep[0].fulavail())[0]),len(indesc1)) if prep != None else None
				nobj = nobj.dpush([(len(indesc1)-len(indesc),len(indesc))]) if nobj != None else self.rows[n].type.emptyinst(len(indesc1),assistmog[n],prep=passprep)#prep is just the actual parameters that need to be prepended.
				oflat = self.rows[n].type.flatten(indesc1,self.rows[n].name,obj=nobj)
				indesc = indesc1.invisadd(oflat)
			fillout = fillout + len(nflat.flat)

		return cu
	def emptyinst(self,limit,mog=False,prep=None):
		if mog == False: mog,limit = striphuman(limit,self.fulavail())
		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)
		assert len(self.rows) == len(mog)
		mog = [mog[i] for i in range(len(mog)) if self.rows[i].obj == None]
		return SubsObject([SubRow(None,self[k].emptyinst(limit,mog[k],prep)) for k in range(len(self))],verdepth=limit)
	def needscarry(self):
		return False
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		if not self.verified: assertstatequal(indesc,self,carry,RefTree(verdepth=len(indesc)))
		outs = []
		oidns = indesc
		indesc.setassumed(None)
		bi = len(indesc)
		for n in range(len(self.rows)):
			if self.rows[n].type == None:
				obj,nty = self.rows[n].obj.verify(indesc,reqtype=True)
			elif type(self.rows[n].type) is Strategy and self.rows[n].type.type == None:
				if any(row.obj==None for row in self.rows[n].type.args.rows):
					gnoa = self.rows[n].type.args.verify(indesc)
					ndsid = indesc.addflat(gnoa.trimallnonessential().flatten(indesc.reroll()))
				else:
					gnoa,ndsid = self.rows[n].type.args.verify(indesc,then=True)

				obj,nty = self.rows[n].obj.verify(ndsid,reqtype=True)
				nty = Strategy(gnoa,nty,verdepth=len(indesc))
				obj = Lambda(gnoa.semavail(),obj,verdepth=len(indesc))
			else:
				nty = self.rows[n].type.verify(indesc,RefTree(verdepth=len(indesc)))
				obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None

			if self.rows[n].name == "*****": self.rows[n].name = nty.fulavail()

			vertype = TypeRow(self.rows[n].name,nty,obj,self.rows[n].silent)
			outs.append(vertype)
			if type(self.rows[n].name) is not list: indesc = indesc.addflat(ScopeObject([vertype]))
			else: indesc = indesc.addflat(nty.flatten(indesc.reroll(),self.rows[n].name,obj=obj))
		outp = DualSubs(outs,pos=self,verdepth=bi,altversion=self.verifyalt(oidns,carry,exob))
		return (outp,indesc) if then else (outp,RefTree(verdepth=bi)) if reqtype else outp
	def peelcompactify(self,indesc,compyoks,then=False,earlyabort=True):
		def _dbgEnter():
			indesc.setSafety(0)
			assert type(compyoks) is tuple
			for j in compyoks[0]:
				assert type(j) is tuple and len(j) == 3
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
				assert type(outp) is DualSubs
				assert type(early) is bool
				outp.setVerified()
				outp.setSafety(len(indesc))


		boo = self.compacrecurse(compyoks[0],[],[],indesc,force=compyoks[1],then=then,earlyabort=earlyabort)
		if boo==None: return None
		return boo
	def compacassign(self,inyoks,overflow=None,cosafety=None,safety=None):
		if cosafety!=None: safety+=cosafety
		prev = False
		for g in inyoks:
			if g[0] != None: prev = True
			elif prev: raise LanguageError(self,"positional argument may not follow keyword argument.")
		def firstnamed(spoken,labels,car,mot=None):
			# more prots
			mot = car.fulavail() if mot == None else mot
			for f in range(len(mot)):
				if car.rows[f].obj != None: continue
				if spoken[f] == True: continue
				if isinstance(mot[f],list):
					if spoken[f] == False: spoken[f] = [False]*len(mot[f])
					k = firstnamed(spoken[f],labels,car.rows[f].type,mot[f])
					if k: return [f] + k
				elif mot[f] == labels[0] or (labels[0] == None and ((cosafety!=None and f<cosafety) or not car.rows[f].silent['silent'])):
					if len(labels) == 1:
						spoken[f] = True
						return [f]
					nxc = car.rows[f].type.type if type(car.rows[f].type.unspool()) is Strategy else car.rows[f].type
					assert type(car.rows[f].type) is DualSubs
					if spoken[f] == False: spoken[f] = [False]*len(nxc)
					k = firstnamed(spoken[f],labels[1:],nxc)
					if k: return [f]+k
		def fullp(spoken):
			if spoken == False: return False
			return spoken == True or all(fullp(k) for k in spoken)
		spoken = [False]*len(self.rows)
		yoks = []
		for s in range(len(inyoks)):
			nan = firstnamed(spoken,[None] if inyoks[s][0] == None else inyoks[s][0],self)
			if nan == None:
				if safety != None and s < safety: return None
				overflow.append(inyoks[s])
			else:
				yoks.append((nan,inyoks[s][1][0],inyoks[s][1][1]))
		return (yoks,fullp(spoken))
	def compacrecurse(self,yoks,trail,prep,indesc,force=False,then=False,earlyabort=False):
		def _dbgEnter():
			indesc.setSafety(0)
			assert type(yoks) is list
			for j in yoks:
				assert type(j) is tuple and len(j) == 3
				if j[2]==False:
					j[1].setSafety(indesc.beginlen())
				else:
					j[1].setSafety(len(indesc)-len(prep))
			self.setVerified()
			self.setSafety(len(indesc))
			# for c in yoks:
			# 	assert "AUUUAUUAUAUAU" not in repr(c)
		def _dbgExit(outp):
			if outp != None:
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
				yoob = reassembled.compacrecurse(yoks,trail,prep,frame,False,then,earlyabort)
				return yoob
			yoob = (ming,frame,reassembled,earlyabort)
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
			rowtype = row.type.verify(indesc.reroll())
			if self.rows[n].obj != None:
				obj = self.rows[n].obj.verify(indesc.reroll()) 
			else:
				obj = None
				lentotal = len(indesc)
				lentho   = len(thot)
				lencom1  = lentotal - lentho
				for k in range(len(yoks)):
					if yoks[k][0] == trail+[n]:
						if yoks[k][2] != False:
							if yoks[k][2] != True:
								othertype = yoks[k][2].dpush([(lentho,lencom1)])
								st = len(yoks)
								if not rowtype.compare(othertype,lencom1,thot,yoks):
									if earlyabort: return None
									raise TypeMismatch(yoks[k][1],rowtype,othertype,indesc)
								ming = getming(thot,st)
								if ming!=None: return restart(thot,ming)
							if rowtype.quickdetect([(-lentho,lencom1)]):
								raise LanguageError(yoks[k][1],"Cannot infer type of parameter")
							obj = yoks[k][1].dpush([(lentho,lencom1)])
							break
						if force:
							obj = yoks[k][1].verify(indesc,rowtype)
							yoks[k] = (yoks[k][0],obj.dpush([(-lentho,lencom1)]),True)
							break
						if type(yoks[k][1].unspool()) is Lambda and not yoks[k][1].obj.needscarry() and type(rowtype.unspool()) is Strategy and len(rowtype.args) == len(yoks[k][1].si):

							trunctype = rowtype.trimallnonessential(yoks[k][1].si)

							try:
								yasat = trunctype.args.ddpush(-lentho,lencom1) if lentho else trunctype.args
							except DDpushError: pass
							else:
								trimmy = indesc.trimabsolute(len(thot))
								# coalesce = 
								earlyabort = False

								yasatflat = yasat.flatten(trimmy.reroll(),yoks[k][1].si)

								nobj,ntyp = yoks[k][1].obj.verify(trimmy.addflat(yasatflat),reqtype=True)
								nsc = longcount(rowtype.args)
								st = len(yoks)
								two = ntyp.dpush([(lentho,lencom1)])

								if not trunctype.type.compare(two,lencom1,thot,yoks):
									#you could theoretically(with sneakinsert) create the real scope object for this comparison.
									print("concern: ",yoks)
									print("nobj: ",nobj.prepr(FormatterObject([k.name for k in trimmy.reroll().flat]+[k.name for k in yasatflat.flat])))
									raise TypeMismatch(yoks[k][1].obj,trunctype.type,two,[k.name for k in indesc.reroll().flat]+[k.name for k in yasatflat.flat])
								ming = getming(thot,st)
								if ming!=None: return restart(thot,ming)
								if rowtype.quickdetect([(-lentho,lencom1)]):
									raise LanguageError(yoks[k][1].obj,"Cannot infer type of parameter")
								obj = Lambda(yoks[k][1].si,nobj.dpush([(lentho,lencom1)]),verdepth=len(indesc))
								yoks[k] = (yoks[k][0],obj.dpush([(-lentho,lencom1)]),True)
								break
						if rowtype.quickdetect([(-lentho,lencom1)]):
							if not force: break
							raise LanguageError(yoks[k][1].obj,"Cannot infer type of parameter")
						earlyabort = False
						obj = yoks[k][1].verify(indesc,rowtype)
						yoks[k] = (yoks[k][0],obj.dpush([(-lentho,lencom1)]),True)
						break
			if any(len(o[0])>len(trail)+1 and o[0][:len(trail)+1] == trail+[n] for o in yoks):
				assert self.rows[n].obj == None
				moro = rowtype.compacrecurse(yoks,trail+[n],thot,indesc,force=force,earlyabort=earlyabort)
				if moro == None: return None
				if len(moro)==3:
					ming,frame,moro,earlyabort = moro
					obj = SubsObject(len(indesc)) if moro.isemptytype() else None
					cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
					reassembled = DualSubs(cu+[self.rows[j] for j in range(n+1,len(self.rows))],verdepth=self.verdepth)
					if trail == ming[:len(trail)]:
						return reassembled.compacrecurse(yoks,trail,prep,frame,False,then,earlyabort)
					return (ming,frame,reassembled,earlyabort)
				moro,earlyabort = moro
				obj = row.obj if row.obj != None else SubsObject(len(indesc)) if moro.isemptytype() else None
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				obj = row.obj.verify(indesc.reroll()) if row.obj != None else obj if obj != None else None
				cu.append(TypeRow(row.name,rowtype,obj,self.rows[n].silent))
			thot = thot+namerical(len(indesc),self.rows[n].name,trail+[n])
			if type(self.rows[n].name) is not list:
				insf = TypeRow(self.rows[n].name,rowtype,obj,self.rows[n].silent)
				indesc = indesc.sneakadd(ScopeObject([insf]))
			else:
				indesc = indesc.sneakadd(self.rows[n].type.flatten(indesc.reroll(),self.rows[n].name,obj=obj))
		for n in range(len(self.rows)):
			for yok in yoks:
				if yok[0] == trail+[n] and cu[n].obj==None:
					raise LanguageError(yok[1],"Cannot infer type of parameter.")
		outp = DualSubs(cu,verdepth=self.verdepth,pos=self)
		return ((outp,earlyabort),indesc) if then else (outp,earlyabort)

	def templaterecurse(self,yoks,trail,indesc,mog,fillout=None):

		if type(mog) is not list: mog = [None]*len(self.rows)
		if fillout == None: fillout = len(indesc.flat)

		cu = []

		for n in range(len(self.rows)):
			row = self.rows[n]
			rowtype = row.type.verify(indesc.reroll())
			if self.rows[n].obj != None:
				obj = self.rows[n].obj.verify(indesc.reroll()) 
			else:
				obj = None
				for k in range(len(yoks)):
					if yoks[k][0] == trail+[n]:
						print("what thefuc ",yoks[k][1],rowtype.prepr(FormatterObject(indesc)))
						obj = yoks[k][1].verify(indesc,rowtype)
						break

			if any(len(o[0])>len(trail)+1 and o[0][:len(trail)+1] == trail+[n] for o in yoks):
				moro = rowtype.templaterecurse(yoks,trail+[n],indesc,mog[n],fillout)
				obj = row.obj if row.obj != None else SubsObject(len(indesc)) if moro.isemptytype() else None
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				obj = row.obj.verify(indesc.reroll()) if row.obj != None else obj if obj != None else None
				cu.append(TypeRow(row.name,rowtype,obj,self.rows[n].silent))

			eu = striphuman(len(indesc),self.rows[n].name)[0]
			if conservativeeq(self.rows[n].name,mog[n]):
				nflat = self.rows[n].type.flatten(indesc.reroll(),mog[n],eu,obj=obj,fillout=fillout)
				indesc = indesc.addflat(nflat)
			else:
				nflat = self.rows[n].type.flatten(indesc,self.rows[n].name,eu,obj=obj,fillout=fillout)
				indesc1 = indesc.sneakinsert(nflat,fillout)
				obj = obj.dpush([(len(indesc1)-len(indesc),len(indesc))]) if obj != None else self.rows[n].type.emptyinst(len(indesc1),eu)
				oflat = self.rows[n].type.flatten(indesc1.reroll(),mog[n],obj=obj)
				indesc = indesc1.invisadd(oflat)
			fillout = fillout + len(nflat.flat)

		return DualSubs(cu,verdepth=self.verdepth,pos=self)





class SubsObject(Tobj):
	@initTobj
	def __init__(self,subs=None,verdepth=None):
		# def _dbgEnter():
		# 	for sub in subs:
		# 		assert type(sub) is SubRow
		self.subs = subs if subs != None else []
		if verdepth!=None:
			self.touches = set()
			self.verdepth = verdepth
			self.complexity = 1
			for sub in self.subs:
				assert type(sub) is SubRow#safemode
				self.touches.update(sub.obj.touches)
				self.complexity += sub.obj.complexity
			# self.touches = {k for k in self.touches if k<verdepth}
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
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		pmultilinecsv(out,indent,self.subs,prepend+context.red("("),context.red(")")+postpend,context,callback=callback)
	def caneasy(self):
		return all(k.obj.caneasy() for k in self.subs)
	def ddpush(self,amt,lim,repls=None,replsrc=None):
		return SubsObject([k.ddpush(amt,lim,repls,replsrc) for k in self.subs],pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc))
	def detect(self,ranges):
		return any(sub.detect(ranges) for sub in self.subs)
	@lazydpush
	def dpush(self,pushes):
		return SubsObject([k.dpush(pushes) for k in self.subs],pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes),altversion=self.dpushalt(pushes))
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other.unspool()) is not SubsObject: return False
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
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		# if reqtype:
		# 	temp = [k.obj.verify(indesc,reqtype=True) for k in self.subs]
		# 	return (SubsObject([SubRow(None,k[0]) for k in temp],verdepth=len(indesc)),DualSubs([TypeRow(None,temp[k][1].dpush([(k,len(indesc))])) for k in range(len(temp))]))

		if self.verified and self.caneasy():
			return SubsObject([SubRow(None,k.obj.verify(indesc)) for k in self.subs],verdepth=len(indesc))

		if carry==None:                           raise LanguageError(self,"type of arguments could not be inferred.")
		if type(carry.unspool()) is not DualSubs: raise LanguageError(self,"type of () object must be a {"+"} object.")
		if exob != None:                          raise LanguageError(self,"{"+"} objects do not accept arguments.")

		oflow = []
		garbo = carry.compacassign(self.phase1(indesc),overflow=oflow)
		if len(oflow):
			raise LanguageError(self,"cannot match with type: "+repr(carry)+"   "+repr(oflow))
		st = carry.peelcompactify(indesc,garbo,earlyabort=False)[0]


		for j in st: assert j.obj != None
		cuu = []
		left = 0
		for g in range(len(st.rows)):
			if carry.rows[g].obj == None:
				cuu.append(SubRow(None,st.rows[g].obj.dpush([(-left,len(indesc))])))
			left += longcount(carry.rows[g].name)
		assert not reqtype
		assert not then
		return SubsObject(cuu,verdepth=len(indesc),pos=self,altversion=self.verifyalt(indesc,carry,exob))
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
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		assert not then
		assertstatequal(indesc,self,carry,RefTree(verdepth=len(indesc)))
		src = self.src.verify(indesc,RefTree(verdepth=len(indesc)),force=True)
		if type(src) is not DualSubs:
			raise LanguageError(self,"Can only apply templating to {"+"} object.")
		if len(self.NSC[0])!=len(self.NSC[1]):
			raise LanguageError(self,"Renaming statements must have an equal number of names on both sides.")
		for k in self.NSC[0]+self.NSC[1]:
			if type(k) is list: raise LanguageError(self,"You can't recursively nest renaming statements.")
		poppo = [(self.NSC[0][a],self.NSC[1][a]) for a in range(len(self.NSC[0]))]
		def triplecopy(ma):
			if type(ma) is str:
				for swap in range(len(poppo)):
					if poppo[swap][0]==ma:
						res = poppo[swap][1]
						del poppo[swap]
						return (res,res)
				return (ma,None)
			if type(ma) is list:
				ra = ([],[])
				for k in ma:
					l = triplecopy(k)
					ra[0].append(l[0])
					ra[1].append(l[1])
				return ra
			return (None,None)
		NANms = triplecopy([a.name for a in src.rows])
		for pop in poppo:
			raise LanguageError(self,"cannot complete renaming statement: "+pop[0]+" was not found.")
		wonk = indesc.addflat(ScopeObject([TypeRow(NANms[1][a],src.rows[a].type,src.rows[a].obj,src.rows[a].silent) for a in range(len(src.rows))]))
		oldcu = [TypeRow(NANms[0][a],src.rows[a].type,src.rows[a].obj,src.rows[a].silent) for a in range(len(src.rows))]+DualSubs(self.rows,verified=False,pos=self).verify(wonk,force=True).rows
		naga = NANms[1]+[a.name for a in self.rows]
		cakewalk = []#(oldindex,length,account,sourceindex)   #always starts with =None except for the first one.
		left = len(indesc)
		nug  = 0
		ac   = 0
		for a in src.rows:
			if a.obj==None:
				cakewalk.append((left,nug,ac))
				left += nug
				nug  = longcount(a.name)
				ac   = 1
			else:
				nug+=longcount(a.name)
				ac+=1
		cakewalk.append((left,nug,ac))
		left+=nug
		nug = 0
		cakestart = len(cakewalk)
		for a in self.rows:
			lc = longcount(a.name)
			cakewalk.append((left,lc,1,a))
			left+=lc
		for starter in range(len(src.rows),len(src.rows)+len(self.rows)):
			pointer = starter
			pastry = cakestart-1
			while pastry>0 and not oldcu[starter].detect([(-cakewalk[pastry][1],cakewalk[pastry][0])]):
				pointer -= cakewalk[pastry][2]
				pastry -= 1
			oldcu.insert(pointer,oldcu.pop(starter))
			naga.insert(pointer,naga.pop(starter))
			cakewalk.insert(pastry+1,cakewalk.pop(cakestart))
			cakestart+=1

		hs = 0
		for a in range(len(cakewalk)):
			tub1 = []
			tub2 = []
			sh=len(indesc)
			for b in cakewalk[:a]:
				if cakewalk[a][0]<b[0]:
					tub1.append((b[1],sh))
				sh+=b[1]
			for b in cakewalk[a+1:]:
				if cakewalk[a][0]>b[0]:
					tub2.append((-b[1],b[0]))
			tub = sorted(tub2,key=lambda x:-x[1])+sorted(tub1,key=lambda x:x[1])
			print("-="*9)
			print(cakewalk)
			print([a.name for a in src.rows])
			print([a.name for a in self.rows])
			print([a.name for a in oldcu])
			print("pushign: ",cakewalk[a],tub)
			for lon in range(hs,hs+cakewalk[a][2]):
				oldcu[lon] = oldcu[lon].dpush(tub)

			hs += cakewalk[a][2]

		cu = DualSubs(oldcu,verdepth=len(indesc),pos=self)
		oflow = []
		garbo = cu.compacassign(SubsObject(self.subs,verified=False,pos=self).phase1_paranoid(),overflow=oflow)[0]
		if len(oflow):
			raise LanguageError(self,"cannot match with type: "+repr(cu)+"   "+repr(oflow))
		outp = cu.templaterecurse(garbo,[],indesc,naga)
		if reqtype: return (outp,RefTree(verdepth=len(indesc)))
		return outp
	@altPrepr
	def prepr(self,context):
		if len(self.NSC[0])==0 and len(self.NSC[1])==0: add=[]
		elif self.NSC[0]==self.NSC[1]: add = [pmultilinelist(self.NSC[0],context)]
		else: add = [pmultilinelist(self.NSC[0],context)+"="+pmultilinelist(self.NSC[1],context)]
		return self.src.prepr(context)+"<"+",".join(add+[k.prepr(context) for k in self.rows]+[k.prepr(context) for k in self.subs])+">"
	@altPmultiline
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		def calls(out,prepend,context_):
			pmultilinecsv(out,indent,self.rows+self.subs,prepend+"<",">"+postpend,context,callback=callback)
		self.src.pmultiline(out,indent,prepend,"",context,calls)
class Lambda(Tobj):
	@initTobj
	def __init__(self,si,obj,verdepth=None):
		# assert type(si) is ScopeIntroducer or type(si) is DualSubs
		self.si = si
		self.obj = obj
		if verdepth!=None:
			# assert False
			self.verdepth = verdepth
			self.complexity = 1+self.obj.complexity
			self.touches = {k for k in self.obj.touches if k<verdepth}
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
			"obj":self.obj.unspool().toJSON()
		}
	def ddpush(self,amt,lim,repls=None,replsrc=None):
		return Lambda(self.si,self.obj.ddpush(amt,lim,repls,replsrc),pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc))
	def detect(self,ranges):
		return self.obj.detect(ranges)
	@lazydpush
	def dpush(self,pushes):
		return Lambda(self.si,self.obj.dpush(pushes),pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes),altversion=self.dpushalt(pushes))
	def caneasy(self):
		return False
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other.unspool()) is not Lambda: return False
		return conservativeeq(self.si,other.si) and self.obj.compare(other.obj,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		if len(self.si) == 0: return self.obj.needscarry()
		return True
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		if exob != None and len(exob.subs) < len(self.si):
			return Lambda(self.si[:len(exob.subs)],Lambda(self.si[len(exob.subs):],self.obj,verified=False,pos=self),verified=False,pos=self,altversion=self.altversion).verify(indesc,carry,reqtype,then,exob,force=True)
		if len(self.si) > len(carry.args):
			return Lambda(self.si[:len(carry.args)],Lambda(self.si[len(carry.args):],self.obj,verified=False,pos=self),verified=False,pos=self,altversion=self.altversion).verify(indesc,carry,reqtype,then,exob,force=True)

		if len(self.si) == 0: return self.obj.verify(indesc,carry,reqtype,then,exob)
		assert not reqtype
		if carry==None:                           raise LanguageError(self,"type of arguments could not be inferred.")
		if type(carry.unspool()) is not Strategy:

			
			raise LanguageError(self,"lambda provided to non-lambda type.")

		scary = carry.trimallnonessential(self.si)
		truncargs = DualSubs(scary.args.rows[:len(self.si)],verdepth=len(indesc))#+longcount(carry.args.rows[:tmomi])
		advdepth = len(indesc)+longcount(truncargs)
		if len(self.si)==len(scary.args.rows):
			ntype = scary.type
		else:
			ntype = Strategy(DualSubs(scary.args.rows[len(self.si):],verdepth=advdepth),scary.type,verdepth=advdepth,pos=carry)
		if exob!=None:
			nnex = SubsObject(exob.subs[len(self.si):],verdepth=len(indesc)) if len(exob.subs)>len(self.si) else None
			exfla = SubsObject(exob.subs[:len(self.si)],verdepth=len(indesc))
			beflat = truncargs.flatten(indesc.reroll(),self.si,obj=exfla)
			yammayam = indesc.invisadd(beflat)
			yamcarry = ntype.verify(indesc.reroll().invisadd(beflat))
			return self.obj.verify(yammayam,yamcarry,exob=nnex,force=True).addalts(self.verifyalt(indesc,carry,exob))
		return self.obj.verify(indesc.addflat(truncargs.flatten(indesc.reroll(),self.si)),ntype).addlambdas(truncargs,self.si)
	@altPrepr
	def prepr(self,context):
		return pmultilinelist(self.si,context)+self.obj.prepr(context.addbits(self.si))
	@altPmultiline
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		self.obj.pmultiline(out,indent,prepend+pmultilinelist(self.si,context),postpend,context.addbits(self.si),callback)
class Strategy(Tobj):
	@initTobj
	def __init__(self,args=None,type=None,verdepth=None):
		self.args = DualSubs(pos=pos,verdepth=verdepth) if args == None else args
		self.type = type
		self.verdepth = verdepth
		if verdepth!=None:
			self.touches = set()
			self.touches.update(self.args.touches)
			self.complexity = 1+self.args.complexity+self.type.complexity
			if self.type!=None:
				self.touches.update(self.type.touches)
			self.touches = {k for k in self.touches if k<verdepth}
	def primToJSON(self):
		return (
			"Strategy",#"type":
			None if self.type==None else self.type.PJID,#"cent":
			[k.PJID for k in self.args.rows]#"rows":
		)
	def toJSON(self):
		return {
			"type":"Strategy",
			"cent":self.type.unspool().toJSON(),
			"rows":self.args.toJSON()["rows"]
		}
	def ddpush(self,amt,lim,repls=None,replsrc=None):
		disgrace = []
		newargs = self.args.ddpush(amt,lim,repls,replsrc,disgrace=disgrace)
		
		newtype = self.type
		if len(disgrace): newtype = newtype.dpush(disgrace)
		newtype = newtype.ddpush(amt,lim,repls,replsrc)
		return Strategy(newargs,newtype,pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt,altversion=self.ddpushalt(amt,lim,repls,replsrc))
	def detect(self,ranges):
		return self.args.detect(ranges,merge=True) or self.type.detect(ranges)
	@lazydpush
	def dpush(self,pushes):
		disgrace = []
		newargs = self.args.dpush(pushes,force=True,disgrace=disgrace)
		newtype = self.type.dpush(disgrace+pushes)
		return Strategy(newargs,newtype,pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes),altversion=self.dpushalt(pushes))
	def caneasy(self):
		return True
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other.unspool()) is not Strategy: return False
		if lefpush==None: lefpush = []
		if rigpush==None: rigpush = []
		adv = []
		st = len(lefpush)
		if not self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush,keepr=True,advanced=adv): return False
		# print(adv)
		if len(adv):
			mdsc = self.verdepth+sum(s[0] for s in lefpush[:st])+longcount(self.args)-longcount([k.name for k in adv])
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
		prep = prep[0].dpush([(limit+sc-prep[1],prep[1])],force=True).subs if prep != None else []

		# disgrace = []
		# self.args.trimallnonessential()
		# newtype = self.type


		return Lambda(self.args.semavail(),self.type.emptyinst(limit+sc,mog,(SubsObject(prep+self.args.emptyinst(limit).subs,verdepth=limit+sc),limit+sc)),verdepth=limit)
	def trimallnonessential(self,si=None):

		disgrace = []
		nargs = self.args.trimallnonessential(si,disgrace)
		ntype = self.type
		if len(disgrace): ntype = ntype.dpush(disgrace)
		return Strategy(nargs,ntype,verdepth=self.verdepth,pos=self)
	@lazyflatten
	def flatten(self,indesc,mog,assistmog,prep=None,obj=None,fillout=None):
		arflat = self.args.flatten(indesc)
		if obj != None:
			sbs = indesc.sneakadd(arflat)
			mascope = indesc.reroll().sneakadd(arflat)
			obj = obj.verify(mascope,self.verify(sbs),exob=self.args.emptyinst(len(indesc)))
		arp = self.args.verify(indesc,force=True)

		if prep == None:
			njprep = (arp,len(indesc))
		else:
			calmdown = prep[0].unspool().dpush([(len(indesc)-longcount(prep[0])-prep[1],prep[1])])
			njprep = (DualSubs(calmdown.rows+arp.rows,verdepth=calmdown.verdepth),len(indesc)-longcount(prep[0]))

		return self.type.flatten(indesc.addflat(arflat),mog,assistmog,njprep,obj,fillout=fillout)
	def needscarry(self):
		if len(self.args) == 0: return self.type.needscarry()
		return False
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		verargs,thendesc = self.args.verify(indesc,then=True)
		if len(verargs) == 0:
			thendesc = thendesc.posterase(len(indesc))
			return self.type.verify(thendesc,carry,reqtype=reqtype,then=then,force=True)#.addalts(self.verifyalt(indesc,carry,exob))

		if not self.verified: assertstatequal(indesc,self,carry,RefTree(verdepth=len(indesc)))
		vertype = self.type.verify(thendesc,RefTree(verdepth=len(thendesc)),then=then)
		if then: vertype,th = vertype
		if type(vertype.unspool()) is Strategy:
			verargs = verargs + vertype.args
			vertype = vertype.type
		outp = Strategy(args=verargs,type=vertype,pos=self,verdepth=len(indesc),altversion=self.verifyalt(indesc,carry,exob))
		return (outp,RefTree(verdepth=len(indesc))) if reqtype else (outp,th) if then else outp
	@altPrepr
	def prepr(self,context):
		res = []
		for k in self.args.rows:
			res.append(k.prepr(context))
			context = context.addbits(k.name)
		return context.red("[")+",".join(res)+context.red("]")+(self.type.prepr(context) if self.type!=None else "None")
	@altPmultiline
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		def calls(out,prepend,context):
			self.type.pmultiline(out,indent,prepend,postpend,context,callback=callback)
		pmultilinecsv(out,indent,self.args.rows,prepend+context.red("["),context.red("]"),context,lamadapt=lambda x:x.name,callback=calls,delim=context.red(","))
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
			self.verdepth = verdepth
			self.complexity = 1+(self.src.complexity if self.src!=None else 0) + self.args.complexity
			self.touches.update(self.args.touches)
			if self.src!=None: self.touches.update(self.src.touches)
			if type(self.name) is int and self.src==None and not self.cold:
				assert self.name<verdepth or self.name==0
				self.touches.add(self.name)

			assert self.src==None or type(self.src) is RefTree or type(self.src.core) is RefTree
			# self.touches = {k for k in self.touches if k<verdepth}
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
			"src":None if self.src==None else self.src.unspool().toJSON()
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
			if not canTranslate(self.name,ranges): return True
		elif self.src.detect(ranges): return True
		return self.args.detect(ranges)
	@lazydpush
	def dpush(self,pushes):
		gy = self.name
		if self.src==None and self.name!=0: gy = translateForward(self.name,pushes)
		# print("ref purshinf ",self,self.getSafety(),pushes,self.altversion,[a.getSafety() for a in self.altversion])
		return RefTree(gy,self.args.dpush(pushes,force=True),None if self.src == None else self.src.dpush(pushes),pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes),altversion=self.dpushalt(pushes),cold=self.cold)
	def setSafety(self,safe):
		if safe == None: return
		if hasattr(self,'foclnsafety'): assert self.foclnsafety == safe
		else:
			self.foclnsafety = safe
			downdeepverify(self,safe)

		if safe!=None:
			if self.src==None and type(self.name) is int and self.name!=0: assert self.name<safe
	def caneasy(self):
		return True
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if self.src != None:
			if type(other.unspool()) is not RefTree: return False
			if other.src == None or not self.src.compare(other.src,odsc,thot,extract,lefpush,rigpush): return False
		elif thot != None:
			for k in thot:
				if k[0] == self.name:
					for j in extract:
						if j[0] == k[1] and j[2] == False:
							return True
					repls = []
					valid = True
					dsc = self.verdepth+sum(g[0] for g in ([] if lefpush==None else lefpush))

					for g1 in range(len(self.args.subs)):
						if type(self.args.subs[g1].obj.unspool()) is not RefTree or self.args.subs[g1].obj.name<odsc:
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
						gr = other.ddpush(odsc+len(repls)-dsc,odsc,repls=repls,replsrc=dsc)
					except DDpushError:
						return False
					mod = gr if len(repls) == 0 else Lambda(["_"]*len(repls),gr,verdepth=odsc)
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(mod)
					extract.append((k[1],mod,True))
					return True
		if type(other.unspool()) is not RefTree: return False
		lefname = self.name
		rigname = other.name
		if lefpush != None:
			for lef in lefpush:
				if lefname>=lef[1]: lefname+=lef[0]
		if rigpush != None:
			for rig in rigpush:
				if rigname>=rig[1]: rigname+=rig[0]
		return lefname == rigname and self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		return False
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert not then
		if type(self.name) is str and self.name.endswith(".ax'"):
			print([k for k in indesc.oprows.dependencies.keys()])
			assert self.name.replace("'","") in indesc.oprows.dependencies
			assertstatequal(indesc,self,carry,RefTree(verdepth=len(indesc)))
			assert exob == None
			tue = indesc.oprows.dependencies[self.name.replace("'","")].dpush([(len(indesc),0)],force=True)

			return (tue,RefTree(verdepth=len(indesc))) if reqtype else tue

		if self.verified and self.args.caneasy() and not reqtype and (self.src==None or self.cold or not indesc.flat[translateForward(self.src.unspool().name,indesc.prepushes)].hasobj() ):
			if self.src == None:
				row = self.name
				for j in indesc.prepushes:
					if row>=j[1]: row += j[0]
				if indesc.flat[row].hasobj():
					pass
				else:
					for j in indesc.postpushes:
						if row>=j[1]: row += j[0]
					subsres = self.args.verify(indesc,force=True)
					if exob != None: subsres = SubsObject(self.args.verify(indesc,force=True).subs+exob.subs,verdepth=len(indesc))
					return RefTree(row,subsres,None if self.src==None else self.src.verify(indesc),pos=self,verdepth=len(indesc),cold=self.cold,altversion=self.verifyalt(indesc,carry,exob))
			else:
				pass

			p1 = self.args.phase1(indesc)

			if exob != None: p1 = p1 + exob.phase1_gentle()
		else:
			p1 = self.args.phase1(indesc)
			if exob != None: p1 = p1 + exob.phase1_gentle()

		if self.src == None:
			tra = indesc.symextract(self.name,p1,carry=carry,reqtype=reqtype,safety=self.safety,verify=not self.verified,pos=self,preventsub=self.cold)
			if tra != None: return (tra[0].addalts(self.verifyalt(indesc,carry,exob)),tra[1]) if reqtype else tra.addalts(self.verifyalt(indesc,carry,exob))
			if self.verified:
				raise LanguageError(self,"Unknown error...")
			if self.name not in [a.name for a in indesc.flat]:
				raise LanguageError(self,"Symbol not defined in this context: "+self.name)
			raise LanguageError(self,"Symbol not defined for these arguments: "+self.name)
		else:
			# indesc.setSafety(0)
			# self.setSafety(indesc.beginlen())
			# self.src.setSafety(indesc.beginlen())
			orig = self.src.verify(indesc,reqtype=True)
			if type(orig[1].unspool()) is DualSubs:
				anguish = orig[1].flatten(indesc.reroll(),obj=orig[0])
				tra = indesc.invisadd(anguish).preerase(len(anguish)).symextract(self.name,p1,carry=carry,reqtype=reqtype,safety=self.safety,verify=not self.verified,limiter=len(indesc.flat),pos=self)
				if tra != None: return (tra[0].addalts(self.verifyalt(indesc,carry,exob)),tra[1]) if reqtype else tra.addalts(self.verifyalt(indesc,carry,exob))
			# if self.name=="construct":
			# 	print(orig[0])
			# 	print(orig[0].altversion)
			for possib in [orig[0].unspool()]+orig[0].altversion:
				if type(possib) is RefTree and possib.src == None and type(self.name) is str:

					retrievalname = indesc.flat[translateBackward(possib.name,indesc.postpushes)].name
					print("RETRIEVALNAME: ",retrievalname)

					tra = indesc.symextract(retrievalname+"."+self.name,possib.args.phase1_gentle()+p1,reqtype=reqtype,carry=carry,safety=self.safety,verify=not self.verified,pos=self,cosafety=len(possib.args.subs))
					if tra != None: return (tra[0].addalts(self.verifyalt(indesc,carry,exob)),tra[1]) if reqtype else tra.addalts(self.verifyalt(indesc,carry,exob))
			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,carry=carry,safety=self.safety+1 if self.safety!=None else None,verify=not self.verified,pos=self)
			if tra != None: return (tra[0].addalts(self.verifyalt(indesc,carry,exob)),tra[1]) if reqtype else tra.addalts(self.verifyalt(indesc,carry,exob))
			raise LanguageError(self,"Symbol not defined for these arguments as a property access, macro, or operator overload: "+self.name)
	@altPrepr
	def prepr(self,context):
		res = str(context.getname(self.name)) if self.src==None else str(self.name)
		if self.src != None: res = self.src.prepr(context)+"."+res
		if len(self.args.subs)>0: res = res+"("+",".join([k.prepr(context) for k in self.args.subs])+")"
		return res
	@altPmultiline
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		def calls(out,prepend,context_):
			res = str(context.getname(self.name)) if self.src==None else str(self.name)
			if len(self.args.subs)==0:
				if callback == None:
					out.append("\t"*indent+prepend+res+postpend)
				else:
					callback(out,prepend+res+postpend,context)
			else:
				pmultilinecsv(out,indent,self.args.subs,prepend+res+"(",")"+postpend,context,callback=callback)
		if self.src == None: calls(out,prepend,context)
		else: self.src.pmultiline(out,indent,prepend,".",context,callback=calls)
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
	@lazyverify
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
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
		def douparse(tree,exob=None,carry=None):
			if len(tree) == 2: return tree
			p1 = [(None,douparse(u)) for u in tree[2]]
			if exob != None: p1 = p1+exob.phase1_gentle()
			ghi = indesc.symextract(tree[0],p1,reqtype=True,carry=carry,safety=len(tree[2]),verify=not self.verified,pos=self)
			if ghi == None:
				if tree[0] not in [a.name for a in indesc.flat]:
					raise LanguageError(self,"operator not defined.")
				raise LanguageError(self,"operator not defined for these arguments.")
			return ghi
		outp = douparse(fulltree[0],exob=exob,carry=None)
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
	def pmultiline(self,out,indent,prepend,postpend,context,callback=None):
		short = self.prepr(context)
		if len(short)+len(prepend)<=context.magic:
			out.append("\t"*indent+prepend+short+postpend)
			return
		rowprep = prepend
		for token in range(len(self.array)):
			if type(self.array[token]) is str:
				rowprep+=self.array[token]+" "
			else:
				if token == len(self.array)-1:
					self.array[token].pmultiline(out,indent,rowprep,postpend,context,callback=callback)
				else:
					self.array[token].pmultiline(out,indent,rowprep,"",context,callback=None)




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
				if type(children[1]) is Strategy:
					obj = Lambda(children[1].args.semavail(),obj,verified=False,pos=meta)
			return TypeRow(children[0][0],children[1],obj,children[0][1])
		obj = None
		if len(children)>1:
			obj = children[1]
			if type(children[0]) is Strategy:
				obj = Lambda(children[0].args.semavail(),obj,verified=False,pos=meta)
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




# 'touches' and 'forbidden' need to be thought about (a lot)

# forbidden-> set of strings representing the names you are not allowed to reference.
# touches-> set of strings you reference

# toPJSON -> (int ref, set of references)



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
	compilefiles({"grouptheory.ax"})
	# compilefiles({"builtin.ax"},redoAll=True)
	# print("debug")


#if the sneeze changes you have to recompile everything.

#if src is reftree and you know it won't get substituted out, you can skeeze.


# _dbgTest()

#flatten could be one-pass, you know. it could perform the same function as verify, which would be mondo cool.
#instead of verify-flatten, just flatten



#add flavored 'then' keyword- silentadd, addflat



#len(indesc) could be stored

#


# game(animation editor)
# hackathon
# this

# minecraft server
# hackathon(eric)


#bring back pos system and get better error tracking.


# push some of the verification to instantiation: a.b must share the same first parameters as a .


 # have multiple channels for refferring back to a specific caller.

# [] needs safety too- [a:jfie,b:ifjei][bn] = |bn|daojsidfioa

# you feel me.

# also you forgot to automatically construct the lambdas i think...
# or notl..


#imports should import everything that matches.


#you have a nice pattern set up... self is in input space, all other arguments are in output space. you can take advantage of this with lazyevaluator.


#list of mangles:

#mangle 2: compact variables (tracked through attached object.)
#mangle 3: when type is Strategy<DualSubs>, wrap self in singleton to try to match it.
	#applies to symextract and lambda
	#when too many lambda arguments are provided, the remainder is wrapped in a singleton and the match is attempted.
#mangle 4: when type is equality in space of DualSubs, accept tuple of equalities.
	#mangle 5: when type is equality in space of functions, accept lambda of equalities.
#mangle 5: when type is [k:K]P and you provide P it should just assume constant.


#you may be able to take some of those dsc functions and give them optional indesc stuff... that way they get a little lazier.


#if the time spent inside the compare function accounts for a significant portion of the runtime, then you should implement a list of previous substitutions to compare instead
#	those ladders may be subbed out already. they vanish when dpush clobbers them.


#you need to fine-tune the operator precidence and associativity.



