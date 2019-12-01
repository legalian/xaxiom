




	def singularindesc(most):
		fod = most[-1]
		for i in reversed(range(len(most)-1)):
			fod = most[i].concatenate(fod)
		return fod








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
	def addlambdas(self,args,si=None,pos=None):
		return self.unspool().addlambdas(args,si,pos)

	# def fulavail(self):
	# 	if type(self.core) is DualSubs or type(self.core) is Strategy: return self.core.fulavail()

	
	def flatten(self,indesc,mog=False,assistmog=None,prep=None,obj=None,fillout=None,then=False,force=False):

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
		if type(mog) is list: raise InvalidSplit()
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
	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		assert False#unimplemented.
		if self.indescs == []: return self.core.pmultiline(context,out,indent,prepend+"|+"+str(sum(k[0] for k in self.postpushes))+"|",postpend,callback)
		return self.core.pmultiline(context,out,indent,prepend+"|"+str(self.indescs[0].beginlen())+"->"+str(len(self.indescs[-1]))+"+"+str(sum(k[0] for k in self.postpushes))+"|",postpend,callback)


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




