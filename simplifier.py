
import copy
from inspect import getfullargspec
from lark import Transformer, v_args, Tree, Lark


from pycallgraph import PyCallGraph
from pycallgraph.output import GraphvizOutput




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
			ahjs.args.setSafety(amt)
		if type(ahjs) is SubsObject:
			for j in ahjs.subs: j.setSafetyrow(amt)
		if type(ahjs) is DualSubs:
			compen = 0
			for j in ahjs.rows:
				j.setSafetyrow(amt+compen)
				compen = compen + longcount(j.name)
		if type(ahjs) is Template:
			ahjs.src.setSafety(amt)
			ahjs.subs.setSafety(amt)
		if type(ahjs) is Lambda:
			if ahjs.sc != None:
				ahjs.obj.setSafety(amt+ahjs.sc)
		if type(ahjs) is Strategy:
			ahjs.args.setSafety(amt)
			ahjs.type.setSafety(amt+longcount(ahjs.args))
	def updeepverify(ahjs):
		if type(ahjs) is RefTree:
			return ahjs.args.getSafety()
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
			if a == None: a = ahjs.subs.getSafety()
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
		safe = self.getSafetyrow()
	else:
		safe = self.getSafety()
	if repls!=None:
		for k in repls:
			k.setSafety(lim)
	if safe == None: return



	assert lim<=safe and lim-amt<=safe




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
def _dbgExit_addfibration(self,dsc,args,outp):
	outp.setVerified()
	outp.setSafety(dsc)



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
		for j in extract:
			j[1].setSafety(odsc)











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



def _dbgEnter_verify(self,indesc,carry,reqtype,then,exob):
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

	if type(outp) is RefTree and outp.src==None and outp.name!=0:
		assert not indesc.flat[translateBackward(outp.name,indesc.postpushes)].hasobj()









class DpushError(Exception):
	pass


class LanguageError(Exception):
	def __init__(self,pos,message):
		message = message + " " + repr(pos)
		super(LanguageError, self).__init__(message)
		self.message = message
		transferlines(self,pos)




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


class ContextYam:
	def __init__(self,operators,dependencies):
		self.operators = operators
		self.dependencies = dependencies


class ScopeObject:
	def __init__(self,flat=None,prpush=None,popush=None,oprows=None):
		self.oprows    = [] if oprows == None else oprows
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
		return ScopeObject(self.flat,self.prepushes+[(len(self)-amt,self.beginlen()+amt-len(self))],self.postpushes,self.oprows)
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
			if safe==0 and type(self.flat[i]) is TypeRow and type(self.flat[i].obj) is RefTree:
				# if self.flat[self.flat[i].obj.name].obj != None:
				# 	self.pprint(0," this failed: ","",40)
				# 	print(self.flat[i])

				cr1=translateBackward(self.flat[i].obj.name,self.postpushes)

				assert self.flat[cr1].obj == None
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
	def symextract(self,name,subs,carry=None,reqtype=False,safety=None,verify=True):
		def _dbgEnter():
			self.setSafety(0)
		def _dbgExit(ahjs):
			if ahjs != None:
				outp = ahjs
				if reqtype:
					outp,ty = ahjs
					ty.setSafety(len(self))
				outp.setVerified()
				outp.setSafety(len(self))


		# print("symextract ",name)
		for k in subs:
			assert len(k) == 2
			assert len(k[1]) == 2
		def compachelper(assign,row):
			if row == 0: return (RefTree(verdepth=len(self)),RefTree(verdepth=len(self))) if reqtype else RefTree(verdepth=len(self))
			cr=translateForwardGentle(row,self.postpushes)

			# self.flat[row].setSafetyrow(cr)

			curr = self.flat[row].unspool().type.dpush([(len(self)-cr,min(cr,len(self)))])

			bedoin = DualSubs(verdepth=len(self))
			cuarg = DualSubs(verdepth=len(self))
			indesc = self
			earlyabort = True
			wsub = subs
			while len(wsub):

				if type(curr.unspool()) is not Strategy: return None
				se = assign(wsub,curr.args)
				if se == None: return None
				shim = curr.args.peelcompactify(indesc,se[0],then=True,earlyabort=earlyabort)
				if shim == None: return None
				wsub = [(y[0],y[1].dpush([(len(shim[1])-len(indesc),len(indesc))]) if y[2]!=False else y[1],y[2] if type(y[2]) is bool else y[2].dpush([(len(shim[1])-len(indesc),len(indesc))])) for y in se[1]]
				bedoin = bedoin + curr.args
				earlyabort=False
				indesc = shim[1]
				cuarg = cuarg+shim[0]

				curr = curr.type

			oldcurr = curr

			yolcur = oldcurr.verify(indesc.reroll(),RefTree(verdepth=len(indesc)))
			curr = yolcur.addfibration(len(self),cuarg)
			if verify: assertstatequal(len(self),None,carry,curr)

			camax = len(cuarg.rows)
			while camax>0 and (cuarg.rows[camax-1].obj==None)==(bedoin.rows[camax-1].obj==None): camax -= 1
			if self.flat[row].obj != None:
				obj = self.flat[row].obj.dpush([(len(self)-cr,min(cr,len(self)))])
			else:
				obj = RefTree(name=cr,verdepth=len(self))
			if camax != 0:

				cuarg = DualSubs(cuarg.rows[:camax],verdepth=cuarg.verdepth)
				bedoin = DualSubs(bedoin.rows[:camax],verdepth=bedoin.verdepth)

				nocue0 = oldcurr.addfibration(len(self),bedoin)
				nocue = nocue0.dpush([(len(indesc)-len(self),len(self))],force=True)
				bodobo = nocue.args.verify(indesc.reroll(),force=True).nonsilent()

				drargs = bedoin.emptyinst(len(self)).verify(indesc.reroll(),bodobo,force=True)

				assert type(drargs) is not LazyEvaluation
				if self.flat[row].obj != None:
					obj = obj.verify(indesc.reroll().preerase(len(self)),nocue,exob=drargs if len(drargs.subs)>0 else None).addlambdas(len(self),cuarg)
				else:
					obj = RefTree(obj.name,drargs,verdepth=len(indesc))
					obj = obj.addlambdas(len(self),cuarg)

			obj.unspool()
			return (obj,curr) if reqtype else obj

		class Scontrol:
			def __init__(self,safety):
				self.safety = safety
			def __call__(self,subs,args):
				oflow = []
				snj = args.compacassign(subs,oflow,self.safety)
				self.safety = None
				return (snj,oflow)
		def momo(subs,args):
			souts = []
			for k in range(len(args)):
				if k>=len(subs):break
				if args.rows[k].obj == None:
					souts.append(([k],subs[k][1][0],subs[k][1][1]))
			return ((souts,True),subs[len(souts):])
		if len(self.flat) == 0 or name == 0: return (RefTree(verdepth=len(self)),RefTree(verdepth=len(self))) if reqtype else RefTree(verdepth=len(self))
		if type(name) is int:
			return compachelper(momo,translateForward(name,self.prepushes))
		else:
			for row in reversed(range(len(self.flat))):
				if self.flat[row].name != name: continue
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
		self.type.setSafety(safe)
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
	def __init__(self,name,ty,obj=None,silent=False):
		self.name = name
		self.type = ty
		self.obj  = obj
		self.silent = silent
		if type(ty) is Lambda or type(ty) is SubsObject: assert False
		assert self.type != None or self.obj != None
		assert type(self.type) is not Strategy or self.type.type != None or self.obj != None
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
		res = "" if self.name == None or context!=None else pprintlist(self.name)+":"
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
		if len(args) == 0:
			return self.dpush([(-longcount(args),dsc)])
		return Strategy(args,self,pos=self,verdepth=dsc)
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
		if not self.verified or exob!=None or reqtype or then or any(indesc.flat[translateForward(i,indesc.prepushes)].hasobj() for i in self.touches):
			return F(self,indesc,carry,reqtype,then,exob,force)
		# print(self,self.touches)
		# m = min(self.touches)
		# pushes = translateForwardPreserve(m,indesc.prepushes)+translateForwardPreserve(translateForward(m,indesc.prepushes),indesc.postpushes)
		# if len(pushes):
		# 	return self.dpush(pushes)

		return self.dpush(indesc.prepushes+indesc.postpushes,force=force)
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
		if self.indescs != []:
			self.core.setSafety(self.indescs[0].beginlen())
			for h in self.indescs:
				h.setSafety(0)

		self.touches = JGIVT

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
		F(self,*args,**kwargs)
		if "verdepth" in kwargs:
			# assert self.verdepth!=-60
			self.setSafety(kwargs.get("verdepth"))

	return wrapper

def lazyverify(F):
	@conditionalverify
	def wrapper(self,indesc,carry=None,reqtype=False,then=False,exob=None,force=False):
		"""dbg_ignore"""
		if self.verified and not then and not force and not reqtype:
			return LazyEvaluation(self,tsSetIndesc(self.touches,indesc),[indesc],carry,None,exob)
		return F(self,indesc,carry,reqtype,then,exob)
	return wrapper

def lazydpush(F):
	def wrapper(self,pushes,force=False):
		"""dbg_ignore"""
		if all(k[0]==0 for k in pushes): return self
		if not force:
			return LazyEvaluation(self,tsSetDpush(self.touches,pushes),None,None,pushes,None)
		return F(self,pushes)
	return wrapper


def lazyflatten(F):
	def wrapper(self,indesc,mog=False,assistmog=None,prep=None,obj=None,trim=False,fillout=None,force=False):
		"""dbg_ignore"""
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
			for sub in self.rows:
				assert type(sub) is TypeRow#safemode
				self.touches.update(sub.type.touches)
				if sub.obj!=None:
					self.touches.update(sub.obj.touches)
			self.touches = {k for k in self.touches if k<verdepth}

	def prepr(self,context=None):
		return "{"+",".join([k.prepr(context=context) for k in self.rows])+"}"
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		pprintcsv(indent,magic,self.rows,prepend+"{","}"+postpend,callback=callback,context=context)
	def nonsilent(self):
		return DualSubs([k.nonsilent() for k in self.rows],pos=self,verdepth=self.verdepth)
	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None):
		left = 0
		cu = []
		for k in range(len(self.rows)):
			cu.append(self.rows[k].ddpush(dsc+left,amt,lim,repls))
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
		limiter = 0
		while lk<len(self.rows) and rk<len(other.rows):
			limiter += 1
			assert limiter<10
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
		def _dbgEnter():
			other.setVerified()
			self.setVerified()
			other.setSafety(self.getSafety())
			self.setSafety(other.getSafety())
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

	@lazyflatten
	@paranoid
	def flatten(self,indesc,mog,assistmog,prep=None,obj=None,fillout=None):
		# if trim: mog = untrim(self,mog)
		# if mog == None: mog = self.fulavail()
		# if obj != None: obj.unspool()
		# # pamt = None
		# if assistmog == None:
		# 	assistmog,ext = striphuman(len(indesc),mog)
		# 	fillout = len(indesc.flat)
		# if type(mog) is not list: return super(Tobj,self).flatten(indesc,mog,assistmog,prep,obj,fillout)
		# if type(obj) is SubsObject: assert len(obj.subs) == len(self)
		# if type(obj) is Lambda and type(obj.obj.unspool()) is SubsObject: assert len(obj.obj.subs) == len(self)
		# assert len(self.rows) == len(mog)

		# yatta = copy.copy(prep)

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
				elif type(obj) is Lambda and type(obj.obj) is SubsObject: nobj = Lambda(obj.si,obj.obj.subs[s].dpush([(len(indesc)-lenold,lenold)]),obj.sc,obj.pos,verdepth=len(indesc))
				else: nobj = RefTree(src=obj,name=s,verdepth=len(indesc))
				s+=1





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
				obj,nty = self.rows[n].obj.verify(indesc,reqtype=True)
			elif type(self.rows[n].type) is Strategy and self.rows[n].type.type == None:
				gnoa,ndsid = self.rows[n].type.args.verify(indesc,then=True)
				obj,nty = self.rows[n].obj.verify(ndsid,reqtype=True)
				nty = Strategy(gnoa,nty,verdepth=len(indesc))
				obj = Lambda(gnoa.semavail(),obj,longcount(gnoa),verdepth=len(indesc))
			else:
				nty = self.rows[n].type.verify(indesc,RefTree(verdepth=len(indesc)))
				obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None

			newname = self.rows[n].name if self.rows[n].name != "*****" else nty.fulavail()

			vertype = TypeRow(newname,nty,obj,self.rows[n].silent)
			outs.append(vertype)
			if type(newname) is not list: indesc = indesc.addflat(ScopeObject([vertype]))
			else: indesc = indesc.addflat(nty.flatten(indesc.reroll(),newname,obj=obj))
		outp = DualSubs(outs,pos=self,verdepth=bi)
		return (outp,indesc) if then else (DualSubs(outs,pos=self,verdepth=len(indesc)),RefTree(verdepth=len(indesc))) if reqtype else outp
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


		sbu = compyoks[0]
		boo = self.compacrecurse(compyoks[0],[],[],indesc,force=compyoks[1],then=then,earlyabort=earlyabort)
		if boo==None: return None
		if then: return boo
		return boo[0]


	def compacassign(self,inyoks,overflow=None,safety=None):
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
				elif mot[f] == labels[0] or (labels[0] == None and not car.rows[f].silent['silent']):
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
			nan = firstnamed(spoken,[None] if inyoks[s][0] == None else inyoke[s][0],self)
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
								# a = rowtype
								# b = yoks[k][2].dpush([(lentho,lencom1)])
								# print("-=-=-=0=-=-=>",indesc)
								# print(a,b,"debug")
								# a.ddpush(0,0,0)
								# b.ddpush(0,0,0)
								# print(a,b,"debug")
								# befothertype = repr(yoks[k][2])

								othertype = yoks[k][2].dpush([(lentho,lencom1)])
								st = len(yoks)
								# print()
								# print()
								if not rowtype.compare(lentotal,othertype,lencom1,thot,yoks):
									# for test in self.rows:
									# 	print("revise")
									# 	test.type.unspool()
									print()
									print(thot)
									print(indesc)
									print()
									print(yoks[k])
									print(rowtype,othertype)
									print("error --------",self,rowtype.prepr(indesc),othertype.prepr(indesc))
									assert False#debugging
									if earlyabort: return None
									assert False
								# DBGDBGDBG = repr(st)+" "+repr(yoks)
								ming = getming(thot,st)
								if ming!=None: return restart(thot,ming)
							# rowtype.setSafety(lentotal)
							# else:
								# print("you integrated",yoks[k][1])
							try: rowtype.ddpush(0,-lentho,lencom1)
							except DpushError:
								# print("debug you")
								# print("\t",tosaue)
								# print("\t",rowtype.prepr(indesc))
								# print("\t",_dbg_enteryoks)
								# print("\t",self)
								# print("\t",n)
								# print("\t",DBGDBGDBG)


								assert False
							obj = yoks[k][1].dpush([(lentho,lencom1)])
							# DBGDBGDBG = "!=False"
							del yoks[k]
							break
						if force:
							obj = yoks[k][1].verify(indesc,rowtype)
							# DBGDBGDBG = "forced"
							del yoks[k]
							break
						if type(yoks[k][1].unspool()) is Lambda and not yoks[k][1].obj.needscarry() and type(rowtype.unspool()) is Strategy and len(rowtype.args) == len(yoks[k][1].si):
							try: yasat = rowtype.args.ddpush(0,-lentho,lencom1)
							except DpushError: pass
							else:
								trimmy = indesc.trimabsolute(len(thot))
								earlyabort = False
								nobj,ntyp = yoks[k][1].obj.verify(trimmy.addflat(yasat.flatten(trimmy,yoks[k][1].si,trim=True)),reqtype=True)
								nsc = longcount(rowtype.args)
								st = len(yoks)
								if not rowtype.type.compare(lentotal+nsc,ntyp.dpush([(lentho,lencom1)]),lencom1,thot,yoks):
									assert False
								ming = getming(thot,st)
								if ming!=None: return restart(thot,ming)
								try: rowtype.ddpush(0,-lentho,lencom1)
								except DpushError: assert False
								obj = Lambda(yoks[k][1].si,nobj.dpush([(lentho,lencom1)]),sc=nsc,verdepth=len(indesc))
								# DBGDBGDBG = "lambda workaround"
								del yoks[k]
								break
						if not force:
							try: rowtype.ddpush(0,-lentho,lencom1)
							except DpushError: break
						earlyabort = False
						obj = yoks[k][1].verify(indesc,rowtype)
						# DBGDBGDBG = "very gently"
						del yoks[k]
						break
			if any(len(o[0])>len(trail)+1 and o[0][:len(trail)+1] == trail+[n] for o in yoks):
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

				# DBGDBGDBG += "morose"
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				# DBGDBGDBG += " not morose "+repr(obj)
				obj = row.obj.verify(indesc.reroll()) if row.obj != None else obj if obj != None else None
				cu.append(TypeRow(row.name,rowtype,obj,self.rows[n].silent))
			thot = thot+namerical(len(indesc),self.rows[n].name,trail+[n])
			if type(self.rows[n].name) is not list:
				insf = TypeRow(self.rows[n].name,rowtype,obj,self.rows[n].silent)

				indesc = indesc.sneakadd(ScopeObject([insf]))
			else:
				indesc = indesc.sneakadd(self.rows[n].type.flatten(indesc.reroll(),self.rows[n].name,obj=obj))
		return (DualSubs(cu,verdepth=self.verdepth),indesc) if then else (DualSubs(cu,verdepth=self.verdepth),earlyabort)
		assert False

class SubsObject(Tobj):
	@initTobj
	def __init__(self,subs=None,verdepth=None):
		self.subs = subs if subs != None else []
		if verdepth!=None:
			self.touches = set()
			self.verdepth = verdepth
			for sub in self.subs:
				assert type(sub) is SubRow#safemode
				self.touches.update(sub.obj.touches)
			self.touches = {k for k in self.touches if k<verdepth}


	def prepr(self,context=None):
		res = "("+",".join([k.prepr(context=context) for k in self.subs])+")"
		if hasattr(self,'foclnsafety') and context==None:
			res = res+"`"+str(self.foclnsafety)+"`"
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
		assert type(carry.unspool()) is DualSubs
		assert exob == None

		oflow = []
		garbo = carry.compacassign(self.phase1(indesc),overflow=oflow)
		if len(oflow):
			raise LanguageError(self,"cannot match with type: "+repr(carry)+"   "+repr(oflow))
		st = carry.peelcompactify(indesc,garbo,force=False)

		for j in st: assert j.obj != None
		cuu = []
		left = 0
		for g in range(len(st.rows)):
			if carry.rows[g].obj == None:
				cuu.append(SubRow(None,st.rows[g].obj.dpush([(-left,len(indesc))])))
			left += longcount(carry.rows[g].name)
		assert not reqtype
		assert not then
		return SubsObject(cuu,verdepth=len(indesc))

class Template(Tobj):
	@initTobj
	def __init__(self,obj,subs):
		assert type(subs) is SubsObject
		self.subs = subs
		self.obj = obj
	def needscarry(self):
		return False
	@lazyverify
	@paranoid
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		#remember to force verification of self.subs.
		# res = self.obj.verify(indesc,RefTree())
		# assert type(res) is DualSubs
		# sob = res.compactify(indesc,carry.phase1(indesc),force=True)
		# if reqtype: (sob,RefTree())
		return "fuka u"
	def prepr(self,context=None):
		return self.obj.prepr(context)+"<"+",".join([k.prepr(context) for k in self.rows])+">"
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			pprintcsv(indent,magic,self.subs.subs,prepend+"<",">"+postpend,callback=callback,context=context)
		self.obj.pprint(indent,prepend,"",magic,calls)

class Lambda(Tobj):
	@initTobj
	def __init__(self,si,obj,sc=None,verdepth=None):
		# assert type(si) is ScopeIntroducer or type(si) is DualSubs
		self.si = si
		self.obj = obj
		self.sc = sc
		if verdepth!=None:
			self.verdepth = verdepth
			self.touches = {k for k in self.obj.touches if k<verdepth}
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
			return Lambda(self.si[:len(exob.subs)],Lambda(self.si[len(exob.subs):],self.obj,verified=False),verified=False).verify(indesc,carry,reqtype,then,exob,force=True)

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
			jsi = self.si + fid.si
			tmomi = carry.args.unulimit(len(jsi))
			truncargs = DualSubs(carry.args.rows[:tmomi],verdepth=len(indesc))
			fid = fid.obj


		untrimmed = untrim(truncargs,jsi)

		jaja,odsc = striphuman(len(indesc),untrimmed)
		allpassalong = truncargs.emptyinst(odsc,jaja)


		# print("as i walk inaosdifjaosdjfoasijdfoasijdf\n\n\n\n")
		elim = 0
		if type(fid) is RefTree and fid.name<len(indesc):
			dsc = odsc
			while elim<len(allpassalong.subs) and elim<len(fid.args.subs):


				if not fid.args.subs[len(fid.args.subs)-1-elim].compare(odsc,allpassalong.subs[len(allpassalong.subs)-1-elim]): break

				while tmomi>0:
					tmomi -= 1
					dsc -= longcount(truncargs.rows[tmomi].name)
					if truncargs.rows[tmomi].obj == None: break

				elim+=1

			if odsc != dsc:
				fid = RefTree(fid.name,SubsObject([k.dpush([(dsc-odsc,dsc)]) for k in fid.args.subs[:len(fid.args.subs)-elim]],verdepth=dsc),fid.src,verdepth=dsc)

		if len(jsi) == elim: return fid
		return Lambda(jsi[:len(jsi)-elim],fid,longcount(truncargs),pos=self,verdepth=len(indesc))

	def addlambdas(self,dsc,args):
		if len(args) == 0: return self
		return Lambda(self.si+args.semavail(),self.obj,None if self.sc == None else self.sc+longcount(args),pos=self,verdepth=self.verdepth)
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
			if self.type!=None:
				self.touches.update(self.type.touches)
			self.touches = {k for k in self.touches if k<verdepth}


	@paranoid
	def ddpush(self,dsc,amt,lim,repls=None):
		return Strategy(self.args.ddpush(dsc,amt,lim,repls),self.type.ddpush(dsc+longcount(self.args),amt,lim,repls),pos=self,verdepth=None if self.verdepth==None else self.verdepth+amt)
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
		arflat = self.args.flatten(indesc)
		if obj != None:
			sbs = indesc.sneakadd(arflat)
			mascope = indesc.reroll().sneakadd(arflat)
			obj = obj.verify(mascope,self.verify(sbs),exob=self.args.emptyinst(len(indesc)))
		arp = self.args.verify(indesc)

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
			self.touches.update(self.args.touches)
			if self.src!=None: self.touches.update(self.src.touches)
			if type(self.name) is int: self.touches.add(self.name)
			self.touches = {k for k in self.touches if k<verdepth}
		assert type(self.args) is SubsObject

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
		if type(other.unspool()) is not RefTree: return False
		if self.src != None:
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
					gr = other.ddpush(dsc,odsc+len(repls)-dsc,odsc,repls=repls)
					mod = gr if len(repls) == 0 else Lambda(["_"]*len(repls),gr,len(repls),verdepth=odsc)
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(odsc,mod)
					extract.append((k[1],mod,True))
					return True
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
		if type(self.name) is str and self.name.endswith(".ax'"):
			print([k for k in indesc.oprows.dependencies.keys()])
			assert self.name.replace("'","") in indesc.oprows.dependencies
			assertstatequal(len(indesc),None,carry,RefTree(verdepth=len(indesc)))
			assert exob == None
			assert not then
			print("\n")
			print(indesc.oprows.dependencies[self.name.replace("'","")])
			print(indesc.oprows.dependencies[self.name.replace("'","")].getSafety())
			print()
			tue = indesc.oprows.dependencies[self.name.replace("'","")].dpush([(len(indesc),0)],force=True)

			return (tue,RefTree(verdepth=len(indesc))) if reqtype else tue



		if self.verified and self.args.caneasy() and not reqtype:
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
					return RefTree(row,subsres,None,pos=self,verdepth=len(indesc))
			else:
				pass#frick frack  #if self.src == None else self.src.verify(indesc)

			p1 = self.args.phase1(indesc)

			if exob != None: p1 = p1 + exob.phase1_gentle()
		else:
			p1 = self.args.phase1(indesc)
			if exob != None: p1 = p1 + exob.phase1_gentle()

		if self.src == None:
			tra = indesc.symextract(self.name,p1,reqtype=reqtype,safety=self.safety,verify=not self.verified)
			if tra != None: return tra
			raise LanguageError(self,"symbol not found")
		else:
			orig = src.verify(self,indesc,reqtype=True)
			if type(orig[1].unspool()) is DualSubs:
				tra = orig[1].flatten(indesc,obj=orig[0]).symextract(self.name,p1,reqtype=reqtype,safety=self.safety,verify=not self.verified)
				if tra != None: return tra
			if type(orig[0].unspool()) is RefTree and orig[0].src == None:
				tra = indesc.symextract(orig[0].name+"."+self.name,orig[0].args.phase1_gentle()+p1,reqtype=reqtype,safety=self.safety,verify=not self.verified)
				if tra != None: return tra
			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,safety=self.safety,verify=not self.verified)
			if tra != None: return tra
			assert False
	def prepr(self,context=None):
		if type(self.name) is int and type(context) is ScopeObject and self.name<len(context):
			res = str(context.flat[translateBackward(self.name,context.postpushes)].name)
		elif hasattr(self,'foclnsafety') and context==None:
			res = str(self.name)+"`"+str(self.foclnsafety)+"`"
		else: res = str(self.name)
		if self.src != None: res = self.src.prepr(context=context)+"."+res
		if len(self.args.subs)>0: res = res+"("+",".join([k.prepr(context=context) for k in self.args.subs])+")"
		return res
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			# if type(self.name) is int and context != None and self.name<len(context):
			# 	res = str(context[self.name])
			# else: res = str(self.name)

			if type(self.name) is int and type(context) is ScopeObject and self.name<len(context):
				res = str(context.flat[translateBackward(self.name,context.postpushes)].name)
			elif hasattr(self,'foclnsafety') and context==None:
				res = str(self.name)+"`"+str(self.foclnsafety)+"`"
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
				if insert == None:
					(prec,nesting) = indesc.precidence(ind)
					shift = fulltree
					while len(shift[-1]) == 3 and shift[-1][1] < prec or shift[-1][1] == prec and nesting:
						shift = shift[-1][2]
					shift[-1] = (ind,prec,[shift[-1]])
					insert = shift[-1][2]
				else:
					urnary = (ind,indesc.precidence(ind)[0],[])
					insert.append(urnary)
					insert = urnary[2]
			else:
				insert.append(ind.verify(indesc,reqtype=True))
				insert = None
		def douparse(tree,exob=None):
			if len(tree) == 2: return tree
			p1 = [(None,douparse(u)) for u in tree[2]]
			if exob != None: p1 = p1+exob.phase1_gentle()
			ghi = indesc.symextract(tree[0],p1,reqtype=True,safety=len(tree[2]),verify=not self.verified)
			if ghi == None: raise LanguageError(self,"operator not defined for these arguments.")
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
					obj = Lambda(children[1].args.semavail(),obj,verified=False)
			return TypeRow(children[0][0],children[1],obj,children[0][1])
		obj = None
		if len(children)>1:
			obj = children[1]
			if type(children[0]) is Strategy:
				obj = Lambda(children[0].args.semavail(),obj,verified=False)
		return TypeRow(None,children[0],obj,{'silent':False,'contractible':False})
	def inferreddeclaration(self,children,meta):
		ty = None if len(children)<3 else Strategy(args=children[1],type=None,verified=False)
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
		return RefTree(name,SubsObject(args,verified=False),src,safety,pos=meta,verified=False)
	def lamb(self,children,meta):
		return Lambda(children[0],children[1],pos=meta,verified=False)
	def template(self,children,meta):
		if len(children): return Template(children[0],children[1],pos=meta,verified=False)
		return Template(children[0],SubsObject(pos=meta,verified=False),pos=meta,verified=False)
	def strategy(self,children,meta):
		args = []
		for j in children[:-1]:
			args += j.rows
		return Strategy(DualSubs(args,verified=False),children[-1],pos=meta,verified=False)
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
		return children[0] if len(children) else SubsObject(pos=meta,verified=False)
	def dualsubs(self,children,meta):
		return DualSubs(children,pos=meta,verified=False)
	def wdualsubs(self,children,meta):
		return children[0] if len(children) else DualSubs(pos=meta,verified=False)






def _dbgTest():
	# print("debug")


	with open("core.lark", "r") as f:
		l = Lark(f.read(),parser='lalr', propagate_positions=True)

	verifiles = {}


	impstack = [{"grouptheory.ax"}]
	active = []
	while len(impstack):
		print(impstack,active,"\n")
		if len(impstack[-1])==0:
			impstack.pop()
			if len(active):
				yis = active.pop()
				ver = yis[1][1].verify(ScopeObject([],oprows=ContextYam(yis[1][0],verifiles)),RefTree(verdepth=0))
				print("\n\nverified",yis[0],":",ver)
				verifiles[yis[0]] = ver
			continue


		filename = impstack[-1].pop()
		if filename in verifiles: continue

		with open(filename, encoding='utf-8') as f: document = f.read()
		transformer = MyTransformer()
		active.append((filename,transformer.transform(l.parse(document))))
		impstack.append(transformer.dependencies)





_dbgTest()

#flatten could be one-pass, you know. it could perform the same function as verify, which would be mondo cool.
#instead of verify-flatten, just flatten



#add flavored 'then' keyword- silentadd, addflat



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



