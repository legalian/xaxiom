
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

	def pprintlist(lis):
		def ppri(sj):
			if type(sj) is not list: return str(sj)
			return "["+",".join([ppri(k) for k in sj])+"]"
		if type(lis) is not list: return str(lis)
		return "|"+",".join([ppri(k) for k in lis])+"|"

	def pprintcsv(indent,magic,lis,head,tail,callback=None,context=None):
		if len(head)<magic:
			lisrepr = [k.prepr(context=context) for k in lis]
			comb = ",".join(lisrepr)
			if len(head)+len(comb)+len(tail)<magic:
				if callback == None:
					print("\t"*indent+head+comb+tail)
				else:
					callback(head+comb+tail,context=context)
				return
		print("\t"*indent+head)
		for k in range(len(lis)):
			lis[k].pprint(indent+1,"","," if k<len(lis)-1 else "",magic,context=context)
		if callback == None:
			print("\t"*indent+tail)
		else:
			callback(tail,context=context)


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


	def assertstatequal(ind,pos,one,two):
		if two != None and one != None:
			if not one.compare(ind,two):
				print(one,type(one))
				print(two,type(two))
				one.pprint(0,"one->","",20)
				two.pprint(0,"two->","",20)
				assert False


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
			if ahjs.sc != None:
				ahjs.obj.setSafety(amt+ahjs.sc)
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
			if ahjs.sc != None:
				just = ahjs.obj.getSafety()
				if just != None: return just-ahjs.sc
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




def translateForward(fug,pushes):
	for amt,lim in pushes:
		if fug>=lim:
			fug+=amt
			assert fug>=lim
	return fug

def translateForwardGentle(fug,pushes):
	# print("do better")
	return translateForward(fug,translateForwardGentlePreserve(fug,pushes))
	# mor = fug
	# for amt,lim in pushes:
	# 	assert amt<=0
	# 	if fug>=lim-amt and mor>=lim: fug+=amt
	# 	if mor>=lim: mor = max(mor+amt,lim)
	# return fug




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








def paranoid(F):
	return F
	def wrapper(*args,**kwargs):
		"""dbg_ignore"""
		global fonodepth
		global fonocolls
		global record
		global fonocollson
		global recordon
		global depth
		fonocolls += 1
		if fonocolls == 50000: assert False

		try:
			fname = F.__name__
			if depth>0:
				fonocollson += 1
				if fname not in recordon:
					recordon[fname] = 1
				else:
					recordon[fname] += 1
			if fname not in record:
				record[fname] = 1
			else:
				record[fname] += 1

			zaru = getfullargspec(F)
			for z in range(len(zaru.args)):
				if zaru.args[z] == 'indesc':
					args[z].setSafety(0)

			for v in args:
				unify(v)
			for k,v in kwargs.items():
				unify(v)

			shouldrecord = (fname == 'addfibration')

			if shouldrecord: depth+=1
			fonodepth += 1
			ahjs = F(*args,**kwargs)
			fonodepth -=1
			if shouldrecord: depth-=1


			if fonodepth == 0:
				print("elapsed calls: ",fonocolls)
				print("histogram: ",record)
				print("elapsed calls(DRS): ",fonocollson)
				print("histogram(DRS): ",recordon)

			unify(ahjs)

		except LanguageError as u:
			relevant = type(args[0]).__name__+"."+F.__name__
			print("-traceback: "+relevant+":")
			for z in range(len(zaru.args)):
				mope = None
				if len(args)>z: mope = args[z]
				elif zaru.args[z] in kwargs: mope = kwargs[zaru.args[z]]
				if hasattr(mope,'pprint'):
					mope.pprint(1,zaru.args[z]+" : ","",50)
				else:
					print("\t"+str(zaru.args[z]),":",mope)
			raise u
		return ahjs
	return wrapper


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
def _dbgEnter_ddpush(self,dsc,amt,lim,repls):
	self.setVerified()
	if type(self) is TypeRow or type(self) is SubRow or type(self) is LazyTypeRow:
		self.setSafetyrow(dsc)
	else:
		self.setSafety(dsc)
	if repls!=None:
		for k in repls:
			k.setSafety(lim)



	assert lim<=dsc and lim-amt<=dsc




def _dbgExit_ddpush(self,dsc,amt,lim,repls,outp):
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
		outp.setSafetyrow(None if safe == None else safe+amt)
	else:
		safe = self.getSafety()
		outp.setSafety(None if safe == None else safe+amt)
		outp.setVerified()


def _dbgEnter_addfibration(self,dsc,args):
	args.setVerified()
	args.setSafety(dsc)
	self.setVerified()
	self.setSafety(dsc+longcount(args))
	# print("ENTER VERIF")
def _dbgExit_addfibration(self,dsc,args,outp):
	outp.setVerified()
	outp.setSafety(dsc)
	# print("EXOT VERIF")



def _dbgEnter_addlambdas(self,dsc,args):
	args.setVerified()
	args.setSafety(dsc)
	self.setVerified()
	self.setSafety(dsc+longcount(args))
def _dbgExit_addlambdas(self,dsc,args,outp):
	outp.setVerified()
	outp.setSafety(dsc)




def _dbgEnter_emptyinst(self,limit,mog,prep):
	if prep!=None:
		prep[0].setVerified()
		prep[0].setSafety(prep[1])
		assert prep[1]<=limit
def _dbgExit_emptyinst(self,limit,mog,prep,ahjs):
	limadd = limit + (longcount(self) if mog == False else 0)
	ahjs.setVerified()
	ahjs.setSafety(limadd)




def _dbgEnter_compare(self,dsc,other,odsc,thot,extract,lefpush,rigpush):
	if extract != None:
		assert odsc != None
		for j in extract:
			if j[2]!=False:
				j[1].setSafety(odsc)#whoops
	# if repr(thot)=="[(49, [0]), (50, [1])]": 
	# 	print("Entering:",thot)
	# 	print("\t",self,other)
	lsum = 0 if lefpush == None else sum(o[0] for o in lefpush)
	rsum = 0 if rigpush == None else sum(o[0] for o in rigpush)
	if type(self) is SubRow or type(self) is TypeRow:
		self.setSafetyrow(dsc+lsum)#first value of compare doesnt match dsc...
		other.setSafetyrow(dsc+rsum)#second value of compare doesnt match dsc...
	else:
		self.setVerified()
		self.setSafety(dsc+lsum)#first value of compare doesnt match dsc...
		other.setVerified()
		other.setSafety(dsc+rsum)#second value of compare doesnt match dsc...

def _dbgExit_compare(self,dsc,other,odsc,thot,extract,lefpush,rigpush,ahjs):
	if extract != None:
		assert odsc != None
		# for j in extract:
		# 	j[1].setSafety(odsc)











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

	if type(outp) is RefTree and outp.src==None and outp.name!=0:
		assert not indesc.flat[translateBackward(outp.name,indesc.postpushes)].hasobj()





class DpushError(Exception):
	pass
class PreverifyError(Exception):
	pass


class LanguageError(Exception):
	def __init__(self,pos,message):
		super(LanguageError, self).__init__(message + " " + repr(pos))
		self.message = message
		# if pos==None: assert False
		transferlines(self,pos)
		# print("123456543fygasdvigasfgvif",self.column,self.row,pos,type(pos))
		# if self.column==0 and self.row==0: assert False



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
		res = self.core.flatten(self.indesc,self.mog,self.assistmog,self.prep,None if self.obj == None else self.obj.unspool(),fillout=self.fillout,trim=False,force=True)
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
	def __init__(self,operators,dependencies):#,lastComputation
		self.operators = operators
		self.dependencies = dependencies
		# self.lastComputation = lastComputation
		# self.nextComputation = Computation()


class ScopeObject:
	def __init__(self,flat=None,prpush=None,popush=None,oprows=None):
		self.oprows     = [] if oprows == None else oprows
		self.prepushes  = [] if prpush == None else [k for k in prpush if k[0]!=0]
		self.postpushes = [] if popush == None else [k for k in popush if k[0]!=0]
		self.flat = [] if flat == None else flat

		assert translateForwardGentle(len(self.flat),self.postpushes) == len(self)

		self.memo = []

		beglen = len(self.flat)
		for amt,lim in reversed(self.prepushes):
			if max(lim,lim+amt)>beglen:
				print(self)
				assert False
			beglen -= amt



	@paranoid
	def addflat(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes,self.oprows)
	@paranoid
	def invisadd(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		if len(newflat.flat) == 0: return self
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes+[(-len(newflat.flat),len(self))],self.oprows)
	@paranoid
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
	@paranoid
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
				# if self.flat[self.flat[i].obj.name].obj != None:
				# 	self.pprint(0," this failed: ","",40)
				# 	print(self.flat[i])

				cr1=translateBackward(self.flat[i].obj.name,self.postpushes)

				assert not self.flat[cr1].hasobj()
				# assert self.flat[i].obj.name<len(self.flat)
				# if len(self.flat[i].obj.args.subs)==0:
					# cr2=self.flat[i].obj.name
					# for j in self.postpushes:
					# 	if cr2>=j[1]-j[0]:cr2+=j[0]

					# one = self.flat[self.flat[i].obj.name].type.dpush([(len(self)-cr1,cr1)]).prepr("dbg")
					# two = self.flat[i].type.dpush([(len(self)-cr,cr)]).prepr("dbg")

					# if one!=two:
					# 	print("\n0-0-0-0-0-0")
					# 	print(self)
					# 	print(i,self.flat[i])
					# 	print(one)
					# 	print(two)
					# 	print("NOT EQUAL\n")
					# 	assert False

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

	
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
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
		pprintcsv(indent,magic,remapflat,prepend+"[[","]]"+postpend+repr(self.postpushes)+" -- "+repr(self.prepushes),callback=callback,context=context)



	@paranoid
	def symextract(self,name,subs,carry=None,reqtype=False,safety=None,verify=True,limiter=None,pos=None,cosafety=None):
		def _dbgEnter():
			self.setSafety(0)
			for j in subs:
				assert type(j) is tuple and len(j) == 2
				assert type(j[1]) is tuple and len(j[1]) == 2
				if j[1][1]==False:
					j[1][0].setSafety(self.beginlen())
				else:
					j[1][0].setSafety(len(self))
		# def _dbgExit(ahjs):
		# 	if ahjs != None:
		# 		outp = ahjs
		# 		if reqtype:
		# 			outp,ty = ahjs
		# 			ty.setSafety(len(self))

		# 		if pos!=None: assert outp.row!=0 or outp.column!=0
		# 		outp.setVerified()
		# 		outp.setSafety(len(self))


		# print("symextract ",name)
		for k in subs:
			assert len(k) == 2
			assert len(k[1]) == 2
		def compachelper(assign,row):
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
				# print("shortstop")
				return (RefTree(verdepth=len(self),pos=pos),RefTree(verdepth=len(self),pos=pos)) if reqtype else RefTree(verdepth=len(self),pos=pos)
			cr=translateForwardGentle(row,self.postpushes)

			# self.flat[row].setSafetyrow(cr)

			curr = self.flat[row].unspool().type.dpush([(len(self)-cr,min(cr,len(self)))])

			bedoin = DualSubs(verdepth=len(self))
			cuarg  = DualSubs(verdepth=len(self))
			indesc = self
			earlyabort = True
			wsub = subs
			mood = []
			while len(wsub):
				if type(curr.unspool()) is not Strategy: return None
				se = assign(wsub,curr.args)
				if se == None: return None
				shim = curr.args.peelcompactify(indesc,se[0],then=True,earlyabort=earlyabort)
				mood = mood+se[0][0]
				if shim == None: return None
				wsub = [(y[0],y[1].dpush([(len(shim[1])-len(indesc),len(indesc))]) if y[2]!=False else y[1],y[2] if type(y[2]) is bool else y[2].dpush([(len(shim[1])-len(indesc),len(indesc))])) for y in se[1]]
				bedoin = bedoin + curr.args
				earlyabort=False
				indesc = shim[1]
				cuarg = cuarg+shim[0]

				curr = curr.type

			oldcurr = curr

			#this is the double verifier slam bam wham


			# curr = oldcurr.verify(indesc.reroll(),RefTree(verdepth=len(indesc))).addfibration(len(self),cuarg)
			if verify or reqtype:
				curr = oldcurr.verify(indesc.reroll(),RefTree(verdepth=len(indesc))).addfibration(len(self),cuarg)
				if verify: assertstatequal(len(self),pos,carry,curr)
			# else:
				# print("wait")

			camax = len(cuarg.rows)
			# while camax>0 and (cuarg.rows[camax-1].obj==None)==(bedoin.rows[camax-1].obj==None): camax -= 1
			if self.flat[row].obj != None:
				obj = self.flat[row].obj.dpush([(len(self)-cr,min(cr,len(self)))])
			else:
				obj = RefTree(name=cr,verdepth=len(self),pos=pos)
			# print(cr,row,"q098w0q9w8e09",self.flat[row].obj,obj)



			if camax != 0:
				# assert False
				# if camax != len(cuarg.rows):
				# 	ldcurr = oldcurr.dpush([(camax-len(cuarg.rows))])
				# 	cuarg  = DualSubs(cuarg.rows[:camax],verdepth=cuarg.verdepth)
				# 	bedoin = DualSubs(bedoin.rows[:camax],verdepth=bedoin.verdepth)

				#it's because you tried to truncate...

				if all([h] in [k[0] for k in mood] for h in range(camax)):
					# for k in 
					# 	assert k[2]==True
					# print("4567890------")
					# print(len(indesc))
					# for k in mood:
					# 	print("\t",k[1].getSafety())
					# 	assert k[2]==True

					drargs = SubsObject([SubRow(None,h[1]) for h in sorted(mood,key=lambda kv:kv[0][0]) if h[0][0]<camax],verdepth=len(self))


					if self.flat[row].obj != None:

						drargs = drargs.dpush([(len(indesc)-len(self),len(self))],force=True)
						# print("-=-=0=0=-0=-0")
						# print(oldcurr.getSafety())
						# print(bedoin.getSafety())
						# print(len(self),longcount(bedoin))
						# print(bedoin)
						# print(cuarg)
						# print([p.name for p in bedoin.rows])
						# print([p.name for p in cuarg.rows])

						nocue = oldcurr.addfibration(len(self),bedoin).dpush([(len(indesc)-len(self),len(self))],force=True)

						obj = obj.verify(indesc.reroll().preerase(len(indesc)-len(self)),nocue,exob=drargs if len(drargs.subs)>0 else None).addlambdas(len(self),cuarg)
					else:
						obj = RefTree(obj.name,drargs,verdepth=len(self),pos=pos)
				else:
					nocue = oldcurr.addfibration(len(self),bedoin).dpush([(len(indesc)-len(self),len(self))],force=True)
					drargs = bedoin.emptyinst(len(self)).verify(indesc.reroll(),nocue.args.unspool().nonsilent(),force=True)

					if self.flat[row].obj != None:
						obj = obj.verify(indesc.reroll().preerase(len(indesc)-len(self)),nocue,exob=drargs if len(drargs.subs)>0 else None)
						# if reducer!=0: obj = obj.dpush([(-reducer,len(self))])
						obj = obj.addlambdas(len(self),cuarg)
					else:
						obj = RefTree(obj.name,drargs,verdepth=len(indesc),pos=pos)
						# if reducer!=0: obj = obj.dpush([(-reducer,len(self))])
						obj = obj.addlambdas(len(self),cuarg)

						print("make addlambdas more cautious...")
						print("make lambda call addlambdas to reduce code redundancy.")

# make addlambdas more cautious...
# make lambda call addlambdas to reduce code redundancy.



			obj.unspool()
			return (obj,curr) if reqtype else obj

		class Scontrol:
			def __init__(self,safety):
				self.safety = safety
			def __call__(self,subs,args):
				oflow = []
				snj = args.compacassign(subs,oflow,cosafety,self.safety)
				self.safety = None
				return (snj,oflow)
		def momo(subs,args):
			souts = []
			for k in range(len(args)):
				if k>=len(subs):break
				if args.rows[k].obj == None:
					souts.append(([k],subs[k][1][0],subs[k][1][1]))
			return ((souts,True),subs[len(souts):])
		if len(self.flat) == 0 or name == 0 and limiter==None:
			# print("shor77777tstop")
			return (RefTree(verdepth=len(self)),RefTree(verdepth=len(self))) if reqtype else RefTree(verdepth=len(self))
		if type(name) is int:
			# print(name,limiter,"goose")
			# print()
			return compachelper(momo,translateForward(name,self.prepushes) if limiter==None else name+limiter)
		else:
			for row in reversed(range(len(self.flat))):
				if limiter!= None and row<limiter: break
				if self.flat[row].name != name: continue
				if limiter== None:
					valid = True
					fug = row
					for amt,lim in reversed(self.prepushes):
						if fug>=lim:
							fug-=amt
							if fug<lim:
								valid = False
					if not valid: continue

				spa = compachelper(Scontrol(safety),row)
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



	@paranoid
	def concatenate(self,other):
		def _dbgEnter():
			self.setSafety(0)
			other.setSafety(0)
			assert len(self) == other.beginlen()
		def _dbgExit(ahjs):
			assert ahjs.beginlen() == self.beginlen()
			assert len(ahjs) == len(other)
			ahjs.setSafety(0)

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

	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None):
		return TypeRow(self.name,self.type.ddpush(dsc,amt,lim,repls),None if self.obj == None else self.obj.ddpush(dsc,amt,lim,repls),self.silent)
	@paranoid
	def dpush(self,pushes):
		return TypeRow(self.name,self.type.dpush(pushes),None if self.obj == None else self.obj.dpush(pushes),self.silent)



	def hasobj(self):
		return self.obj != None

	def vershortcut(self,indesc):
		return TypeRow(self.name,self.type.verify(indesc),None if self.obj == None else self.obj.verify(indesc),self.silent)
	def unspool(self):
		return self


	def prepr(self,context=None):
		res = "" if self.name == None else pprintlist(self.name)+":"
		if self.silent["silent"]:
			if res=="": res = "?:"
			else: res = res[:-1]+"?:"
		if self.type != None: res = res+self.type.prepr(context=context)
		if self.obj != None: res = res+" = "+self.obj.prepr(context=context)
		return res
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			if self.obj != None:
				self.obj.pprint(indent,prepend,postpend,magic,callback=callback,context=context)
			else:
				if callback == None:
					print("\t"*indent+prepend+postpend)
				else:
					callback(prepend+postpend,context=context)
		name = "" if self.name == None else pprintlist(self.name)+":"
		self.type.pprint(indent,prepend+name," = " if self.obj != None else "",magic,calls,context=context)
	def __repr__(self):
		return self.prepr()



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
	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None):
		return SubRow(self.name,self.obj.ddpush(dsc,amt,lim,repls))
	@paranoid
	def dpush(self,pushes):
		return SubRow(self.name,self.obj.dpush(pushes))

	@paranoid
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		return self.obj.compare(dsc,other.obj,odsc,thot,extract,lefpush,rigpush)
	def prepr(self,context=None):
		res = "" if self.name == None or context!=None else pprintlist(self.name)+" = "
		res = res+self.obj.prepr(context=context)
		return res
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		name = "" if self.name == None else pprintlist(self.name)+" = "
		self.obj.pprint(indent,prepend+name,postpend,magic,callback,context=context)
	def __repr__(self):

		return self.prepr()



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

	@paranoid
	def flatten(self,indesc,mog,assistmog=None,prep=None,obj=None,fillout=None,trim=False,force=False):
		        #self,indesc,mog,assistmog,prep=None,obj=None,fillout=None
		# if not hasattr(self,'flattens'): self.flattens = 0
		# self.flattens += 1
		# if self.flattens>1: print("tobj",self.flattens)


		assert not trim
		if type(mog) is list: raise LanguageError(self,"invalid renamer pattern.")
		if prep != None: njprep = prep[0].unspool().dpush([(len(indesc)-longcount(prep[0])-prep[1],prep[1])],force=True)
		if prep == None or len(njprep.rows)==0:
			return ScopeObject([TypeRow(mog,self.verify(indesc),None if obj == None else obj)])
		else:
			spap = len(indesc)-longcount(njprep)

			t1 = self.verify(indesc).addfibration(spap,njprep)

			t2 = None if obj == None else obj.addlambdas(spap,njprep)

			return ScopeObject([TypeRow(mog,t1,t2)])
	@paranoid
	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not int: raise LanguageError(self,"invalid renamer pattern.")
		prep = None if prep == None else prep[0].dpush([(limit-prep[1],prep[1])])

		return RefTree(name=mog,args=prep,verdepth=limit)
	@paranoid
	def addfibration(self,dsc,args):

# def _dbgEnter_addfibration(self,dsc,args):
# 	args.setVerified()
# 	args.setSafety(dsc)
# 	self.setVerified()
# 	self.setSafety(dsc+longcount(args))
# def _dbgExit_addfibration(self,dsc,args,outp):
# 	outp.setVerified()
# 	outp.setSafety(dsc)

		if len(args) == 0:
			return self.dpush([(-longcount(args),dsc)])

		return Strategy(args,self,verdepth=dsc,pos=self)
	def addlambdas(self,dsc,args):
		if len(args) == 0:
			return self.dpush([(-longcount(args),dsc)])
		return Lambda(args.semavail(),self,longcount(args),pos=self,verdepth=dsc)
	def unspool(self):
		return self
		pass
	def __repr__(self):
		return self.prepr()




def conditionalverify(F):
	def wrapper(self,indesc,carry=None,reqtype=False,then=False,exob=None,force=False):
		"""dbg_ignore"""
		if not self.verified or (exob!=None and type(self) is not RefTree) or reqtype or then or any(len(indesc.flat) and indesc.flat[translateForward(i,indesc.prepushes)].hasobj() for i in self.touches):
			# print("conditions causeing repeat: ",self.verified,exob,reqtype,then,self.touches if self.verified else None,self)
			return F(self,indesc,carry,reqtype,then,exob,force)
		# print(self,self.touches)
		# m = min(self.touches)
		# pushes = translateForwardPreserve(m,indesc.prepushes)+translateForwardPreserve(translateForward(m,indesc.prepushes),indesc.postpushes)
		# if len(pushes):
		# 	return self.dpush(pushes)


		if len(indesc.prepushes) or len(indesc.postpushes):
			self = self.dpush(indesc.prepushes+indesc.postpushes,force=force)

		if exob!=None:
			self = RefTree(self.name,SubsObject(self.args.subs+exob.subs,verdepth=self.verdepth),self.src,verdepth=self.verdepth,pos=self)

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

	@paranoid
	def emptyinst(self,limit,mog=False,prep=None):
		return self.unspool().emptyinst(limit,mog,prep)


	def caneasy(self):
		return self.core.caneasy() 

	def needscarry(self):
		return True

	@paranoid
	def addfibration(self,dsc,args):
		return self.unspool().addfibration(dsc,args)
	@paranoid
	def addlambdas(self,dsc,args):
		return self.unspool().addlambdas(dsc,args)

	# def fulavail(self):
	# 	if type(self.core) is DualSubs or type(self.core) is Strategy: return self.core.fulavail()

	
	@paranoid
	def flatten(self,indesc,mog=False,assistmog=None,prep=None,obj=None,fillout=None,trim=False,force=False):



		if trim or mog==False:
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

			t1 = moto.addfibration(spap,njprep)

			t2 = None if obj == None else obj.addlambdas(spap,njprep)

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
		return self.prepr()
	def prepr(self,context=None):
		if self.indescs == []: return "|+"+str(sum(k[0] for k in self.postpushes))+"|"+self.core.prepr(context=context)
		return "|"+str(self.indescs[0].beginlen())+"->"+str(len(self.indescs[-1]))+"+"+str(sum(k[0] for k in self.postpushes))+"|"+self.core.prepr(context=context)
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		if self.indescs == []: return self.core.pprint(indent,prepend+"|+"+str(sum(k[0] for k in self.postpushes))+"|",postpend,magic,callback,context)
		return self.core.pprint(indent,prepend+"|"+str(self.indescs[0].beginlen())+"->"+str(len(self.indescs[-1]))+"+"+str(sum(k[0] for k in self.postpushes))+"|",postpend,magic,callback,context)


	def setVerified(self):
		pass
		pass
	def ddpush(self,dsc,amt,lim,repls=None):
		return self.unspool().ddpush(dsc,amt,lim,repls)
	@paranoid
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		return self.unspool().compare(dsc,other,odsc,thot,extract,lefpush,rigpush)
	@paranoid
	def dpush(self,pushes,force=False):
		res = LazyEvaluation(self.core,tsSetDpush(self.touches,pushes),self.indescs,self.carry,self.postpushes+[k for k in pushes if k[0]!=0],self.exob)
		if force: return res.unspool()
		return res
	@conditionalverify
	@paranoid
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None,force=False):
		assert not reqtype
		if then: return self.unspool().verify(indesc,carry,reqtype,then,exob)

		if self.exob == None: bex = exob
		elif exob == None: bex = self.exob.verify(indesc,carry,force=True)
		else:
			bex = SubsObject(self.exob.verify(indesc,carry,force=True).subs+exob.subs,verdepth=len(indesc))

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
	def wrapper(self,*args,pos=None,verified=True,alternates=None,**kwargs):
		"""dbg_ignore"""
		transferlines(self,pos)
		self.verified = verified
		self.altversions = [] if alternates == None else alternates
		self.verdepth = None
		self.complexity = 0
		self.PJID = None
		F(self,*args,**kwargs)
		if "verdepth" in kwargs:
			# assert self.verdepth!=-60
			self.setSafety(kwargs.get("verdepth"))
			for k in self.touches:
				assert k==0 or k<self.verdepth
		# else:
		# 	assert self.row!=0 or self.column!=0

	return wrapper

def lazyverify(F):
	@conditionalverify
	def wrapper(self,indesc,carry=None,reqtype=False,then=False,exob=None,force=False):
		"""dbg_ignore"""
		force=True#dbgdbg

		if self.verified and not then and not force and not reqtype and self.complexity> 2:
			return LazyEvaluation(self,tsSetIndesc(self.touches,indesc),[indesc],carry,None,exob)
		return F(self,indesc,carry,reqtype,then,exob)
	return wrapper

def lazydpush(F):
	def wrapper(self,pushes,force=False):
		"""dbg_ignore"""
		force=True#dbgdbg


		if all(k[0]==0 for k in pushes): return self
		if not force and self.complexity> 2:
			return LazyEvaluation(self,tsSetDpush(self.touches,pushes),None,None,pushes,None)
		return F(self,pushes)
	return wrapper


def lazyflatten(F):
	def wrapper(self,indesc,mog=False,assistmog=None,prep=None,obj=None,trim=False,fillout=None,force=False):
		"""dbg_ignore"""
		force=True#dbgdbg

		# assert False

		sel = self if type(self) is DualSubs else self.type if type(self) is Strategy else None
		if trim: mog = untrim(sel.unspool(),mog)
		if mog == False: mog = sel.fulavail()
		# pamt = None
		if assistmog == None:
			assistmog,ext = striphuman(len(indesc),mog)
			fillout = len(indesc.flat)
		if type(mog) is not list: return Tobj.flatten(self,indesc,mog,assistmog,prep,obj,fillout=fillout)
		if len(sel.fulavail()) != len(mog): raise LanguageError(self,"wrong number of labels for flattening.")
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

	def prepr(self,context=None):
		return "{"+",".join([k.prepr(context=context) for k in self.rows])+"}"
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		pprintcsv(indent,magic,self.rows,prepend+"{","}"+postpend,callback=callback,context=context)
	def nonsilent(self):
		return DualSubs([k.nonsilent() for k in self.rows],pos=self,verdepth=self.verdepth)
	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None,disgrace=None):
		disgrace = [] if disgrace == None else disgrace
		left = 0
		cu = []

		# simul<><<>>S<D<><>SDF<><>D<SF

		# self.setSafety(dsc)
		for k in range(len(self.rows)):
			try:
				m = self.rows[k]
				# m.setSafetyrow(dsc+left-(sum(k[0] for k in disgrace)))
				if len(disgrace): m = m.dpush(disgrace)
				m = m.ddpush(dsc+left,amt,lim,repls)
			except DpushError as u:
				# assert False
				if self.rows[k].obj == None: raise u
				disgrace.append((-longcount(self.rows[k].name),dsc+left))
			else:
				cu.append(m)
				left += longcount(self.rows[k].name)
		return DualSubs(cu,verdepth=None if self.verdepth==None else self.verdepth+amt)
	@lazydpush
	@paranoid
	def dpush(self,pushes):
		return DualSubs([i.dpush(pushes) for i in self.rows],pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes))


	def caneasy(self):
		return True

	@paranoid
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other.unspool()) is not DualSubs: return False
		if len(self) != len(other): return False
		if lefpush == None: lefpush = []
		if rigpush == None: rigpush = []
		lk = 0
		rk = 0
		# limiter = 0
		while lk<len(self.rows) and rk<len(other.rows):
			# limiter += 1
			# assert limiter<10
			if self.rows[lk].obj != None:
				jl = longcount(self.rows[lk].name)
				lefpush = lefpush + [(-jl,dsc)]
				lk += 1
			if other.rows[rk].obj != None:
				jr = longcount(other.rows[rk].name)
				rigpush = rigpush + [(-jr,dsc)]
				rk += 1
			if self.rows[lk].obj==None and self.rows[rk].obj==None:
				if not conservativeeq(self.rows[lk].name,other.rows[rk].name): return False
				if not self.rows[lk].type.compare(dsc,other.rows[rk].type,odsc,thot,extract,lefpush,rigpush): return False
				j = longcount(self.rows[lk].name)
				dsc += j
				lk += 1
				rk += 1
		return True
	def unulimit(self,momin):
		tmomi = -1
		mopass = 0
		while mopass<=momin:
			tmomi += 1
			if tmomi>=len(self.rows) or self.rows[tmomi].obj == None: mopass += 1
		return tmomi
	def append(self,other):
		return DualSubs(self.rows+[other],verdepth=self.verdepth)
	def __add__(self,other):
		# def _dbgEnter():
		# 	other.setVerified()
		# 	self.setVerified()
		# 	other.setSafety(self.getSafety())
		# 	self.setSafety(other.getSafety())
		return DualSubs(self.rows+other.rows,verdepth=self.verdepth)
	def __len__(self):
		return len([k for k in self.rows if k.obj == None])
	def __getitem__(self, key):#must be verified first
		return [k for k in self.rows if k.obj == None][key].type
	def fulavail(self):
		return [j.name for j in self.rows]
	def semavail(self,mog=False):
		if mog == False: mog = self.fulavail()
		return [self.rows[k].type.semavail(mog[k]) if type(mog[k]) is list else mog[k] for k in range(len(self.rows)) if self.rows[k].obj == None]

	def trimallnonessential(self,dsc):
		disgrace = [] if disgrace == None else disgrace
		left = 0
		cu = []
		for k in range(len(self.rows)):
			if self.rows[k].obj == None: 
				m = self.rows[k]
				if len(disgrace): m = m.dpush(disgrace)
				cu.append(m)
				left += longcount(self.rows[k].name)
			else:
				disgrace.append((-longcount(self.rows[k].name),dsc+left))
		return DualSubs(cu,verdepth=self.verdepth)

	@lazyflatten
	@paranoid
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
				elif type(obj) is Lambda and type(obj.obj) is SubsObject: nobj = Lambda(obj.si,obj.obj.subs[s].dpush([(len(indesc)-lenold,lenold)]),obj.sc,obj.pos,verdepth=len(indesc),pos=obj)
				else: nobj = RefTree(src=obj.dpush([(len(indesc)-lenold,lenold)]),name=s,verdepth=len(indesc),pos=obj)
				s+=1

			# print(nobj.)



			nflat = self.rows[n].type.flatten(indesc,mog[n],assistmog[n],prep,obj=nobj,fillout=fillout)
			cu.flat += nflat.flat

			if conservativeeq(self.rows[n].name,mog[n]) and prep == None:

				indesc = indesc.addflat(nflat)
			else:
				indesc1 = indesc.sneakinsert(nflat,fillout)


				passprep = (prep[0].emptyinst(len(indesc1),striphuman(len(indesc1)-longcount(prep[0]),prep[0].fulavail())[0]),len(indesc1)) if prep != None else None
				# intermed = 
				nobj = nobj.dpush([(len(indesc1)-len(indesc),len(indesc))]) if nobj != None else self.rows[n].type.emptyinst(len(indesc1),assistmog[n],prep=passprep)#prep is just the actual parameters that need to be prepended.


				oflat = self.rows[n].type.flatten(indesc1,self.rows[n].name,obj=nobj)#<---- this part...

				indesc = indesc1.invisadd(oflat)
			fillout = fillout + len(nflat.flat)

		# if pamt != None: return cu.dpush(pamt[0],pamt[1])
		return cu


		# you forgot to dpush backwards afterwards...
	@paranoid
	def emptyinst(self,limit,mog=False,prep=None):
		if mog == False: mog,limit = striphuman(limit,self.fulavail())
		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)
		assert len(self.rows) == len(mog)
		mog = [mog[i] for i in range(len(mog)) if self.rows[i].obj == None]
		return SubsObject([SubRow(None,self[k].emptyinst(limit,mog[k],prep)) for k in range(len(self))],verdepth=limit)

	def needscarry(self):
		return False
	@lazyverify
	@paranoid
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		if not self.verified: assertstatequal(len(indesc),self,RefTree(verdepth=len(indesc)),carry)
		outs = []
		bi = len(indesc)
		for n in range(len(self.rows)):
			if self.rows[n].type == None:
				print("|||||>",self.rows[n])
				obj,nty = self.rows[n].obj.verify(indesc,reqtype=True)
			elif type(self.rows[n].type) is Strategy and self.rows[n].type.type == None:
				print("|||||>",self.rows[n])
				gnoa,ndsid = self.rows[n].type.args.verify(indesc,then=True)
				obj,nty = self.rows[n].obj.verify(ndsid,reqtype=True)
				nty = Strategy(gnoa,nty,verdepth=len(indesc))
				obj = Lambda(gnoa.semavail(),obj,longcount(gnoa),verdepth=len(indesc))
			else:
				nty = self.rows[n].type.verify(indesc,RefTree(verdepth=len(indesc)))
				obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None

			if self.rows[n].name == "*****": self.rows[n].name = nty.fulavail()

			vertype = TypeRow(self.rows[n].name,nty,obj,self.rows[n].silent)
			outs.append(vertype)
			if type(self.rows[n].name) is not list: indesc = indesc.addflat(ScopeObject([vertype]))
			else: indesc = indesc.addflat(nty.flatten(indesc.reroll(),self.rows[n].name,obj=obj))
		outp = DualSubs(outs,pos=self,verdepth=bi)
		return (outp,indesc) if then else (outp,RefTree(verdepth=bi)) if reqtype else outp
	@paranoid
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
				assert type(outp) is DualSubs
				outp.setVerified()
				outp.setSafety(len(indesc))


		boo = self.compacrecurse(compyoks[0],[],[],indesc,force=compyoks[1],then=then,earlyabort=earlyabort)
		if boo==None: return None
		if then: return boo
		return boo[0]


	# when verifying a.whatever, a little extra verification is warranted. ---->>>> not so.
	# also it might have too many or too little parameters and then youre fucked.
	# 	too few->instantly fail
	# 	too many->instantly fail
	# 	so not that bad.


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
	@paranoid
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
				else:
					outp,early = outp
					assert type(early) is bool
				assert type(outp) is DualSubs
				outp.setVerified()
				outp.setSafety(len(indesc))

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
			tosaue = rowtype.prepr(indesc)
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
								if not rowtype.compare(lentotal,othertype,lencom1,thot,yoks):
									if earlyabort and False: return None#dbgdbg<><>TODOTODO
									raise LanguageError(yoks[k][1],"Expected: "+rowtype.prepr(context=indesc)+" Got: "+othertype.prepr(context=indesc))
								ming = getming(thot,st)
								if ming!=None: return restart(thot,ming)
							try: rowtype.ddpush(lentotal,-lentho,lencom1)
							except DpushError:
								print(self,yoks)
								raise LanguageError(yoks[k][1],"Cannot infer type of parameter")
							obj = yoks[k][1].dpush([(lentho,lencom1)])
							break
						if force:
							obj = yoks[k][1].verify(indesc,rowtype)
							yoks[k] = (yoks[k][0],obj.dpush([(-lentho,lencom1)]),True)
							break
						if type(yoks[k][1].unspool()) is Lambda and not yoks[k][1].obj.needscarry() and type(rowtype.unspool()) is Strategy and len(rowtype.args) == len(yoks[k][1].si):
							try: yasat = rowtype.args.ddpush(lentotal,-lentho,lencom1)
							except DpushError: pass
							else:
								trimmy = indesc.trimabsolute(len(thot))
								earlyabort = False

								nobj,ntyp = yoks[k][1].obj.verify(trimmy.addflat(yasat.flatten(trimmy.reroll(),yoks[k][1].si,trim=True)),reqtype=True)
								nsc = longcount(rowtype.args)
								st = len(yoks)
								two = ntyp.dpush([(lentho,lencom1)])

								if not rowtype.type.compare(lentotal+nsc,two,lencom1,thot,yoks):
									raise LanguageError(yoks[k][1].obj,"Expected: "+rowtype.type.prepr(context=indesc)+" Got: "+two.prepr(context=indesc))
								ming = getming(thot,st)
								if ming!=None: return restart(thot,ming)
								try: rowtype.ddpush(lentotal,-lentho,lencom1)
								except DpushError:
									raise LanguageError(yoks[k][1].obj,"Cannot infer type of parameter")
								obj = Lambda(yoks[k][1].si,nobj.dpush([(lentho,lencom1)]),sc=nsc,verdepth=len(indesc))
								yoks[k] = (yoks[k][0],obj.dpush([(-lentho,lencom1)]),True)
								break
						if not force:
							try: rowtype.ddpush(lentotal,-lentho,lencom1)
							except DpushError: break
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
		outp = DualSubs(cu,verdepth=self.verdepth,pos=self)
		return (outp,indesc) if then else (outp,earlyabort)
		

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


	def prepr(self,context=None):
		res = "("+",".join([k.prepr(context=context) for k in self.subs])+")"
		if hasattr(self,'foclnsafety') and context==None:
			res = res#+"`"+str(self.foclnsafety)+"`"
		return res
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		pprintcsv(indent,magic,self.subs,prepend+"(",")"+postpend,callback=callback,context=context)

	def caneasy(self):#verified and caneasy
		return all(k.obj.caneasy() for k in self.subs)

	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None):
		return SubsObject([k.ddpush(dsc,amt,lim,repls) for k in self.subs],pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt)
	@lazydpush
	@paranoid
	def dpush(self,pushes):
		return SubsObject([k.dpush(pushes) for k in self.subs],pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes))

	@paranoid
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other.unspool()) is not SubsObject: return False
		if len(self.subs) != len(other.subs): return False
		return all(self.subs[k].compare(dsc,other.subs[k],odsc,thot,extract,lefpush,rigpush) for k in range(len(self.subs)))
	@paranoid
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
	def needscarry(self):
		return True
	@lazyverify
	@paranoid
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		if self.verified and self.caneasy():
			return SubsObject([SubRow(None,k.obj.verify(indesc)) for k in self.subs],verdepth=len(indesc))

		if carry==None:                           raise LanguageError(self,"type of arguments could not be inferred.")
		if type(carry.unspool()) is not DualSubs: raise LanguageError(self,"type of () object must be a {"+"} object.")
		if exob != None:                          raise LanguageError(self,"{"+"} objects do not accept arguments.")

		oflow = []
		garbo = carry.compacassign(self.phase1(indesc),overflow=oflow)
		if len(oflow):
			raise LanguageError(self,"cannot match with type: "+repr(carry)+"   "+repr(oflow))
		st = carry.peelcompactify(indesc,garbo)

		for j in st: assert j.obj != None
		cuu = []
		left = 0
		for g in range(len(st.rows)):
			if carry.rows[g].obj == None:
				cuu.append(SubRow(None,st.rows[g].obj.dpush([(-left,len(indesc))])))
			left += longcount(carry.rows[g].name)
		assert not reqtype
		assert not then
		return SubsObject(cuu,verdepth=len(indesc),pos=self)

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
	@paranoid
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		assert not then
		assertstatequal(len(indesc),self,carry,RefTree(verdepth=len(indesc)))
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
		cu = DualSubs([TypeRow(NANms[0][a],src.rows[a].type,src.rows[a].obj,src.rows[a].silent) for a in range(len(src.rows))] + DualSubs(self.rows,verified=False,pos=self).verify(wonk,force=True).rows,verdepth=len(indesc),pos=self)
		oflow = []
		garbo = cu.compacassign(SubsObject(self.subs,verified=False,pos=self).phase1(indesc),overflow=oflow)
		if len(oflow):
			raise LanguageError(self,"cannot match with type: "+repr(cu)+"   "+repr(oflow))
		outp = cu.peelcompactify(indesc,garbo)
		if reqtype: return (outp,RefTree(verdepth=len(indesc)))
		return outp



	def prepr(self,context=None):
		return self.src.prepr(context)+"<"+",".join([k.prepr(context) for k in self.rows]+[k.prepr(context) for k in self.subs])+">"
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			pprintcsv(indent,magic,self.rows+self.subs,prepend+"<",">"+postpend,callback=callback,context=context)
		self.src.pprint(indent,prepend,"",magic,calls)

class Lambda(Tobj):
	@initTobj
	def __init__(self,si,obj,sc=None,verdepth=None):
		# assert type(si) is ScopeIntroducer or type(si) is DualSubs
		self.si = si
		self.obj = obj
		self.sc = sc
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
			"obj":self.obj.unspool().toJSON(),
			"sc":self.sc
		}

	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None):
		return Lambda(self.si,self.obj.ddpush(dsc+self.sc,amt,lim,repls),self.sc,pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt)
	@lazydpush
	@paranoid
	def dpush(self,pushes):
		return Lambda(self.si,self.obj.dpush(pushes),self.sc,pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes))


	def caneasy(self):
		return False

	@paranoid
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other.unspool()) is not Lambda: return False
		assert self.sc == other.sc
		return conservativeeq(self.si,other.si) and self.obj.compare(dsc+self.sc,other.obj,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		if len(self.si) == 0: return self.obj.needscarry()
		return True
	@lazyverify
	@paranoid
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):

		if exob != None and len(exob.subs) < len(self.si):
			return Lambda(self.si[:len(exob.subs)],Lambda(self.si[len(exob.subs):],self.obj,verified=False,pos=self),verified=False,pos=self).verify(indesc,carry,reqtype,then,exob,force=True)

		if len(self.si) == 0: return self.obj.verify(indesc,carry,reqtype,then,exob)
		assert not reqtype
		if carry==None:                           raise LanguageError(self,"type of arguments could not be inferred.")
		if type(carry.unspool()) is not Strategy: raise LanguageError(self,"lambda provided to non-lambda type.")
		if len(self.si) > len(carry.args):        raise LanguageError(self,"too many lambda arguments provided.")
		tmomi = carry.args.unulimit(len(self.si))
		truncargs = DualSubs(carry.args.rows[:tmomi],verdepth=len(indesc))#+longcount(carry.args.rows[:tmomi])

		advdepth = len(indesc)+longcount(truncargs)

		ntype = carry.type.addfibration(advdepth,DualSubs(carry.args.rows[tmomi:],verdepth=advdepth))
		if exob == None:
			fid = self.obj.verify(indesc.addflat(truncargs.flatten(indesc.reroll(),self.si,trim=True)),ntype)
		else:
			nnex = SubsObject(exob.subs[len(self.si):],verdepth=len(indesc)) if len(exob.subs)>len(self.si) else None
			exfla = SubsObject(exob.subs[:len(self.si)],verdepth=len(indesc))

			beflat = truncargs.flatten(indesc.reroll(),self.si,obj=exfla,trim=True)

			yammayam = indesc.invisadd(beflat)
			yamcarry = ntype.verify(indesc.reroll().invisadd(beflat))

			return self.obj.verify(yammayam,yamcarry,exob=nnex,force=True)

		jsi = self.si
		if type(fid.unspool()) is Lambda:
			print("ONE:",jsi,untrim(truncargs,jsi),fid.getSafety(),"======",fid.sc,carry.args.rows)
			jsi = self.si + fid.si
			tmomi = carry.args.unulimit(len(jsi))
			truncargs = DualSubs(carry.args.rows[:tmomi],verdepth=len(indesc))
			fid = fid.obj
			print("attention")
			print("TWO:",jsi,untrim(truncargs,jsi),fid.getSafety())
		else:
			print("nah")


		untrimmed = untrim(truncargs,jsi)

		jaja,odsc = striphuman(len(indesc),untrimmed)
		allpassalong = truncargs.emptyinst(odsc,jaja)#<<<<<------ this sure doesn't work at all...


		# print("as i walk inaosdifjaosdjfoasijdfoasijdf\n\n\n\n")
		elim = 0
		if type(fid) is RefTree and fid.name<len(indesc):
			dsc = odsc
			while elim<len(allpassalong.subs) and elim<len(fid.args.subs):
				break#TODOTODOTODO<><><><>DBGDBGdbgdbg

				if not fid.args.subs[len(fid.args.subs)-1-elim].compare(odsc,allpassalong.subs[len(allpassalong.subs)-1-elim]): break

				while tmomi>0:
					tmomi -= 1
					dsc -= longcount(truncargs.rows[tmomi].name)
					if truncargs.rows[tmomi].obj == None: break

				elim+=1

			if odsc != dsc:
				fid = RefTree(fid.name,SubsObject([k.dpush([(dsc-odsc,dsc)]) for k in fid.args.subs[:len(fid.args.subs)-elim]],verdepth=dsc),fid.src,verdepth=dsc)

		if len(jsi) == elim: return fid
		return Lambda(jsi[:len(jsi)-elim],fid,longcount(untrimmed),pos=self,verdepth=len(indesc))

	def addlambdas(self,dsc,args):
		if len(args) == 0: return self

# def _dbgEnter_addlambdas(self,dsc,args):
# 	args.setVerified()
# 	args.setSafety(dsc)
# 	self.setVerified()
# 	self.setSafety(dsc+longcount(args))
# def _dbgExit_addlambdas(self,dsc,args,outp):
# 	outp.setVerified()
# 	outp.setSafety(dsc)

		return Lambda(self.si+args.semavail(),self.obj,None if self.sc == None else self.sc+longcount(args),pos=self,verdepth=dsc)
	def prepr(self,context=None):
		return pprintlist(self.si)+self.obj.prepr(context)
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		self.obj.pprint(indent,prepend+pprintlist(self.si),postpend,magic,callback,context)

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



	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None):
		disgrace = []
		newargs = self.args.ddpush(dsc,amt,lim,repls,disgrace=disgrace)
		
		# self.type.setSafety(dsc+longcount(self.args))

		newtype = self.type
		if len(disgrace): newtype = newtype.dpush(disgrace)
		newtype = newtype.ddpush(dsc+longcount(newargs),amt,lim,repls)

		return Strategy(newargs,newtype,pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt)
	@lazydpush
	@paranoid
	def dpush(self,pushes):
		return Strategy(self.args.dpush(pushes),self.type.dpush(pushes),pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes))

	def caneasy(self):
		return True

	@paranoid
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other.unspool()) is not Strategy: return False
		return self.args.compare(dsc,other.args,odsc,thot,extract,lefpush,rigpush) and self.type.compare(dsc+longcount(self.args),other.type,odsc,thot,extract,lefpush,rigpush)
	@paranoid
	def addfibration(self,dsc,args):
		# print("-=-=-=-")
		# print(self.getSafety())
		# print(dsc)
		# print(args.getSafety())
		return Strategy(args+self.args,self.type,pos=self,verdepth=dsc)
	def fulavail(self):
		return self.type.fulavail()
	def semavail(self,mog):
		return self.type.semavail(mog)
	@paranoid
	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)
		sc = longcount(self.args)
		if prep == None: prep = (SubsObject(verdepth=limit),limit)
		prep = prep[0].dpush([(limit+sc-prep[1],prep[1])],force=True).subs if prep != None else []
		return Lambda(self.args.semavail(),self.type.emptyinst(limit+sc,mog,(SubsObject(prep+self.args.emptyinst(limit).subs,verdepth=limit+sc),limit+sc)),sc=sc,verdepth=limit)

	@lazyflatten
	@paranoid
	def flatten(self,indesc,mog,assistmog,prep=None,obj=None,fillout=None):

		# if not hasattr(self,'flattens'): self.flattens = 0
		# self.flattens += 1
		# if self.flattens>1: print("strat",self.flattens)


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
	@paranoid
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		verargs,thendesc = self.args.verify(indesc,then=True)
		if len(verargs) == 0:
			thendesc = thendesc.posterase(len(indesc))
			return self.type.verify(thendesc,carry,reqtype=reqtype,then=then,force=True)

		if not self.verified: assertstatequal(len(indesc),self,RefTree(verdepth=len(indesc)),carry)
		vertype = self.type.verify(thendesc,RefTree(verdepth=len(thendesc)),then=then)
		if then: vertype,th = vertype
		if type(vertype.unspool()) is Strategy:
			verargs = verargs + vertype.args
			vertype = vertype.type
		outp = Strategy(args=verargs,type=vertype,pos=self,verdepth=len(indesc))
		return (outp,RefTree(verdepth=len(indesc))) if reqtype else (outp,th) if then else outp
	def prepr(self,context=None):
		return "["+",".join([k.prepr(context=context) for k in self.args.rows])+"]"+(self.type.prepr(context=context) if self.type!=None else "None")
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			self.type.pprint(indent,prepend,postpend,magic,callback=callback,context=context)
		pprintcsv(indent,magic,self.args.rows,prepend+"[","]",callback=calls,context=context)

class RefTree(Tobj):
	@initTobj
	def __init__(self,name=None,args=None,src=None,safety=None,verdepth=None):
		self.name   = 0 if name == None else name
		self.args   = SubsObject(verdepth=verdepth) if args == None else args
		self.src    = src
		self.safety = safety
		if verdepth!=None:
			self.touches = set()
			self.verdepth = verdepth
			self.complexity = 1+(self.src.complexity if self.src!=None else 0) + self.args.complexity
			self.touches.update(self.args.touches)
			if self.src!=None: self.touches.update(self.src.touches)
			if type(self.name) is int and self.src==None:
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


	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None):
		gy = self.name
		if gy >= lim and self.src == None:
			gy += amt
			if gy-(0 if repls==None else len(repls)) < lim:
				if repls == None: raise DpushError
				fom = self.ddpush(dsc,lim-dsc,lim)#dsc->odsc    lim-amt-len(repls)?
				for j in range(len(repls)):
					if fom.compare(lim,repls[j]): return RefTree(lim+j,verdepth=dsc+amt)
				raise DpushError
		return RefTree(gy,self.args.ddpush(dsc,amt,lim,repls),None if self.src == None else self.src.ddpush(dsc,amt,lim,repls),pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt)
	@lazydpush
	@paranoid
	def dpush(self,pushes):
		gy = self.name if self.src!=None or self.name==0 else translateForward(self.name,pushes)
		return RefTree(gy,self.args.dpush(pushes,force=True),None if self.src == None else self.src.dpush(pushes),pos=self,verdepth=None if self.verdepth==None else self.verdepth+sum(k[0] for k in pushes))

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

	@paranoid
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if self.src != None:
			if type(other.unspool()) is not RefTree: return False
			if other.src == None or not self.src.compare(dsc,other.src,odsc,thot,extract,lefpush,rigpush): return False
		elif thot != None:
			for k in thot:
				if k[0] == self.name:
					for j in extract:
						if j[0] == k[1] and j[2] == False: return True
					repls = []
					valid = True
					for g1 in range(len(self.args.subs)):
						if type(self.args.subs[g1].obj.unspool()) is not RefTree or self.args.subs[g1].obj.name<odsc:
							valid = False
							break
						for g2 in range(g1):
							if self.args.subs[g1].obj.compare(dsc,self.args.subs[g2].obj):
								valid = False
								break
						if not valid: break
						repls.append(self.args.subs[g].obj)
					if not valid: break
					print(">>>>>>>>>>>>>>",dsc,odsc,len(repls))
					print("\t",self,other)
					try:
						gr = other.ddpush(dsc,odsc+len(repls)-dsc,odsc,repls=repls)
					except DpushError:
						raise u#dbgdbg<><><><>TODOTODO

						return False
					mod = gr if len(repls) == 0 else Lambda(["_"]*len(repls),gr,len(repls),verdepth=odsc)
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(odsc,mod)
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
		return lefname == rigname and self.args.compare(dsc,other.args,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		return False
	@lazyverify
	@paranoid
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert not then
		if type(self.name) is str and self.name.endswith(".ax'"):
			print([k for k in indesc.oprows.dependencies.keys()])
			assert self.name.replace("'","") in indesc.oprows.dependencies
			assertstatequal(len(indesc),None,carry,RefTree(verdepth=len(indesc)))
			assert exob == None
			# print("\n")
			# print(indesc.oprows.dependencies[self.name.replace("'","")])
			# print(indesc.oprows.dependencies[self.name.replace("'","")].getSafety())
			# print()
			tue = indesc.oprows.dependencies[self.name.replace("'","")].dpush([(len(indesc),0)],force=True)

			return (tue,RefTree(verdepth=len(indesc))) if reqtype else tue

		# assert self.verified or not self.veronce
		# self.veronce=True

		if self.verified and self.args.caneasy() and not reqtype and (self.src==None or not indesc.flat[translateForward(self.src.unspool().name,indesc.prepushes)].hasobj() ):
			if self.src == None:
				row = self.name
				for j in indesc.prepushes:
					if row>=j[1]: row += j[0]
				if indesc.flat[row].hasobj():
					# print("\thadobj:",self,indesc.flat[row])
					pass
				else:
					for j in indesc.postpushes:
						if row>=j[1]: row += j[0]
					subsres = self.args.verify(indesc,force=True)
					if exob != None: subsres = SubsObject(self.args.verify(indesc,force=True).subs+exob.subs,verdepth=len(indesc))
					return RefTree(row,subsres,None if self.src==None else self.src.verify(indesc),pos=self,verdepth=len(indesc))
			else:
				pass#frick frack  #if self.src == None else self.src.verify(indesc)

			p1 = self.args.phase1(indesc)

			if exob != None: p1 = p1 + exob.phase1_gentle()
		else:
			# if self.verified and not self.args.caneasy():
			# 	print("easyness!!!",self)
			# print("-=-=-==-=-=-=->",self.verified,self.args.caneasy(),reqtype,self)
			p1 = self.args.phase1(indesc)
			if exob != None: p1 = p1 + exob.phase1_gentle()

		if self.src == None:
			tra = indesc.symextract(self.name,p1,reqtype=reqtype,safety=self.safety,verify=not self.verified,pos=self)
			if tra != None: return tra
			if self.name not in [a.name for a in indesc.flat]:
				raise LanguageError(self,"Symbol not defined in this context.")
			raise LanguageError(self,"Symbol not defined for these arguments.")
		else:
			# indesc.setSafety(0)
			# self.setSafety(indesc.beginlen())
			# self.src.setSafety(indesc.beginlen())
			orig = self.src.verify(indesc,reqtype=True)
			if type(orig[1].unspool()) is DualSubs:
				anguish = orig[1].flatten(indesc.reroll(),obj=orig[0])
				# p1p = [p if p[1][1]!=False else (p[0],(p[1][0].dpush([(len(anguish),len(indesc))]),False)) for p in p1]


				# print(indesc.beginlen(),len(indesc))
				# print(indesc.invisadd(anguish).preerase(len(anguish)).beginlen(),len(indesc.invisadd(anguish).preerase(len(anguish))))


				tra = indesc.invisadd(anguish).preerase(len(anguish)).symextract(self.name,p1,reqtype=reqtype,safety=self.safety,verify=not self.verified,limiter=len(indesc.flat),pos=self)
				if tra != None: return tra
			if type(orig[0].unspool()) is RefTree and orig[0].src == None and type(self.name) is str:


#     tra = indesc.symextract(orig[0].name+"."+self.name,orig[0].args.phase1_gentle()+p1,reqtype=reqtype,safety=self.safety,verify=not self.verified,pos=self)
# TypeError: unsupported operand type(s) for +: 'int' and 'str'
				retrievalname = indesc.flat[translateBackward(orig[0].name,indesc.postpushes)].name
				# print("oueir"*4,retrievalname)

				tra = indesc.symextract(retrievalname+"."+self.name,orig[0].args.phase1_gentle()+p1,reqtype=reqtype,safety=self.safety,verify=not self.verified,pos=self,cosafety=len(orig[0].args.subs))
				if tra != None: return tra
			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,safety=self.safety+1,verify=not self.verified,pos=self)
			if tra != None: return tra
			assert False
	def prepr(self,context=None):
		if type(self.name) is int and type(context) is ScopeObject and self.name<len(context) and self.src==None:
			res = str(context.flat[translateBackward(self.name,context.postpushes)].name)
		elif hasattr(self,'foclnsafety') and context==None:
			res = str(self.name)#+"`"+str(self.foclnsafety)+"`"
		else: res = str(self.name)
		if self.src != None: res = self.src.prepr(context=context)+"."+res
		if len(self.args.subs)>0: res = res+"("+",".join([k.prepr(context=context) for k in self.args.subs])+")"
		return res
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			# if type(self.name) is int and context != None and self.name<len(context):
			# 	res = str(context[self.name])
			# else: res = str(self.name)

			if type(self.name) is int and type(context) is ScopeObject and self.name<len(context) and self.src == None:
				res = str(context.flat[translateBackward(self.name,context.postpushes)].name)
			elif hasattr(self,'foclnsafety') and context==None:
				res = str(self.name)#+"`"+str(self.foclnsafety)+"`"
			else: res = str(self.name)

			# assert context!=None

			if len(self.args.subs)==0:
				if callback == None:
					print("\t"*indent+prepend+res+postpend)
				else:
					callback(prepend+res+postpend,context=context)
			else:
				pprintcsv(indent,magic,self.args.subs,prepend+res+"(",")"+postpend,callback=callback,context=context)
		if self.src == None: calls(prepend,context=context)
		else: self.src.pprint(indent,prepend,".",magic,callback=calls,context=context)

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
	@paranoid
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
		def douparse(tree,exob=None):
			if len(tree) == 2: return tree
			p1 = [(None,douparse(u)) for u in tree[2]]
			if exob != None: p1 = p1+exob.phase1_gentle()
			ghi = indesc.symextract(tree[0],p1,reqtype=True,safety=len(tree[2]),verify=not self.verified,pos=self)
			if ghi == None:
				if tree[0] not in [a.name for a in indesc.flat]:
					raise LanguageError(self,"operator not defined.")
				raise LanguageError(self,"operator not defined for these arguments.")
			return ghi
		outp = douparse(fulltree[0],exob=exob)
		return outp if reqtype else outp[0]
	def prepr(self,context=None):
		ssa = []
		for k in self.array:
			if type(k) is str: ssa.append(k)
			elif type(k) is OperatorSet: ssa.append("("+k.prepr(context=context)+")")
			else: ssa.append(k.prepr(context=context))
		return " ".join(ssa)
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		short = self.prepr(context=context)
		if len(short)+len(prepend)<=magic:
			print("\t"*indent+prepend+short+postpend)
			return
		rowprep = prepend
		for token in range(len(self.array)):
			if type(self.array[token]) is str:
				rowprep+=self.array[token]+" "
			else:
				if token == len(self.array)-1:
					self.array[token].pprint(indent,rowprep,postpend,magic,callback=callback,context=context)
				else:
					self.array[token].pprint(indent,rowprep,"",magic,callback=None,context=context)





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
		# print("-=-=-=-=-=-",children,[type(c) for c in children])
		# if len(children) == 1 and children[0].name==None:
		# 	return children[0].obj
		# print()
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
		return Lambda(json["si"],self.generic(json["obj"],depth+json["sc"]),json["sc"],verdepth=depth)




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
	compilefiles({"grouptheory.ax"})
	# compilefiles({"grouptheory.ax"})
	# compilefiles({"builtin.ax"})
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



