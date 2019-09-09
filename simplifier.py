


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


def assertstatequal(pos,a,b,speciala=None):
	jasdf



def untrim(car,mosh):
	if type(mosh) is not list: return mosh
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


def longcount(jj):
	if type(jj) is DualSubs: return sum(longcount(k.name) for k in jj.rows)
	if type(jj) is list: return sum(longcount(k) for k in jj)
	return 1

def trimlongcount(car,jj):
	return longcount(untrim(car,jj))


def striphuman(limit,h):
	flim = limit
	def strip(h):
		if type(h) is list: return [strip(k) for k in h]
		flim = flim + 1
		return flim - 1
	return strip(h)




class ScopeObject:
	def __init__(self,flat,prpush=None,popush=None,singlep=None,dualp=None):
		self.singlep    = [] if singlep == None else singlep
		self.dualp      = [] if dualp == None else dualp
		self.prepushes  = [] if prpush == None else prpush
		self.postpushes = [] if popush == None else popush
		self.flat = flat
	def addflat(self,newflat):
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes,self.singlep,self.dualp)

	def trimabsolute(self,amt):
		return ScopeObject(self.flat[:-amt],self.prepushes,self.postpushes,self.singlep,self.dualp)



	# newflat is in the coordinate space of self



# [A:U]uprove:A

# uprove()


# - extraction
# - substitution (A for [C]D)
# - flattening


# can i substitute it for something and then compare it?
# a lambda can. during the comparison phase.
# -include alternating/racing lambdas.








	def prepush(self,amt,lim):
		return ScopeObject(self.flat,self.prepushes+[(amt,lim)],self.postpushes,self.singlep,self.dualp)
	def postpush(self,amt,lim):
		ylim = lim
		for ya in self.postpushes:
			if ylim>=ya[1]: ylim += ya[0]
		return ScopeObject([self.flat[fg].dpush(None,amt,lim) if fg>=ylim else self.flat[fg] for fg in range(len(self.flat))],self.prepushes,self.postpushes+[(amt,lim)],self.singlep,self.dualp)
	def beginlen(self):
		return len(self.flat) - sum([l for l in self.prepushes])
	def __len__(self):
		return len(self.flat) + sum([l for l in self.postpushes])


	def reroll(self):#be careful with reroll...
		return ScopeObject(self.flat,[(-j[0],j[1]) for j in reversed(self.postpushes)],self.postpushes,self.singlep,self.dualp)


	def symextract(self,name,subs,carry=None,reqtype=False,safety=None):
		def compachelper(assign,row):
			cr=row
			for j in self.postpushes:
				if cr>=j[1]:cr+=j[0]
			curr = self.rows[row].type.dpush(None,len(self)-cr,cr)
			bedoin = DualSubs()
			cuarg = DualSubs()
			indesc = self
			earlyabort=True
			wsub = subs
			while True:
				se = assign(wsub,curr.args)
				if se == None: return None
				shim = curr.args.peelcompactify(indesc,se[0],then=True,earlyabort=earlyabort)
				if shim == None: return None
				wsub = [(y[0],y[1].dpush(len(shim[1])-len(indesc),len(indesc)),y[2] if type(y[2]) is bool else y[2].dpush(len(shim[1])-len(indesc),len(indesc))) for y in se[1]]
				bedoin = bedoin + curr.args
				earlyabort=False
				indesc = shim[1]
				cuarg = cuarg+shim[0]
			curr = curr.verify(indesc.reroll())
			assertstatequal(None,carry,curr.addfibration(cuarg))
			obj = self.flat[row].obj.dpush(None,len(self)-cr,cr) if self.flat[row].obj != None else self.flat[row].type.emptyinst(len(self),cr)
			camax = len(cuarg.rows)
			while camax>0 and (cuarg.rows[camax-1].obj==None)==(bedoin.rows[camax-1].obj==None): camax -= 1
			if camax == 0: return obj
			cuarg = DualSubs(cuarg.rows[:camax])
			bedoin = DualSubs(bedoin.rows[:camax])

			safetime = obj.claimlambda(self.reroll(),bedoin,bedoin.emptyinst(self.beginlen()).verify(indesc)).addlambdas(cuarg)
			safetime.foclnsafety = len(self)#safemode
			return safetime
		yamt = safety
		def scontrol(subs,args):
			oflow = []
			snj = subs.compacassign(subs,oflow,yamt)
			yamt = None
			return (snj,oflow)
		def momo(subs,args):
			souts = []
			for k in range(len(args)):
				if k>=len(subs):break
				if args.rows[k].obj == None:
					souts.append(([k],subs[k][1],subs[k][2]))
			return (souts,subs[len(souts):])
		if type(name) is int:
			row = name
			for j in self.postpushes:
				if row>=j[1]: row += j[0]
			return compachelper(momo,row)
		else:
			row = len(self.flat)-1
			while True:
				yamt = safety
				spa = compachelper(scontrol)
				if spa == None: continue
				return spa
				if row == 0: return None
				row-=1







class TypeRow:
	def __init__(self,name,type,obj=None,silent=False):
		# assert type(name) is str or name == None or type(name) is list#safemode
		self.name = name
		self.type = type
		self.obj  = obj
		self.silent = silent
	def dpush(self,dsc,amt,lim,repls=None):
		return TypeRow(self.name,self.type.dpush(dsc,amt,lim,repls),None if self.obj == None else self.obj.dpush(dsc,amt,lim,repls),self.silent)
	def compare(self,dsc,other,odsc=None,thot=None,extract=None):
		if not self.type.compare(dsc,other.type,odsc,thot,extract): return False
		if self.obj == None: return True 
		return other.obj != None and self.obj.compare(dsc,other.obj,odsc,thot,extract)


class SubRow:
	def __init__(self,name,obj):
		# assert type(name) is str or name == None or type(name) is list#safemode
		self.name = name
		self.obj  = obj
	def dpush(self,dsc,amt,lim,repls=None):
		return SubRow(self.name,self.obj.dpush(dsc,amt,lim,repls))
	def compare(self,dsc,other,odsc=None,thot=None,extract=None):
		return self.obj.compare(dsc,other.obj,odsc,thot,extract)



class Tobj:
	def flatten(self,indesc,mog,assistmog=None,prep=None,obj=None):
		if type(mog) is list: ErrorObject.fatal(self,"invalid renamer pattern.")
		if prep == None or len(prep[0])==0:
			return ScopeObject([TypeRow(mog,self.verify(indesc),obj.verify(indesc))])
		else:
			njprep = prep[0].dpush(None,len(indesc)-prep[1],prep[1])
			return ScopeObject([TypeRow(mog,self.verify(indesc).addfibration(njprep),None if obj == None else obj.verify(indesc).addlambdas(njprep))])

	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not int: ErrorObject.fatal(self,"invalid renamer pattern.")
		safetime = RefTree(name=mog,args=prep[0].dpush(None,limit-prep[1],prep[1]) if prep != None else SubsObject())
		safetime.foclnsafety = limit
		return safetime
	def addfibration(self,args):
		if len(args) == 0: return self
		return Strategy(args,self,pos=self)
	def addlambdas(self,args):
		if len(args) == 0: return self
		return Lambda(args.semavail(),self,longcount(args),pos=self)
	def claimlambda(self,indesc,tyargs,args):
		if len(args) == 0: return self
		shra = copy.copy(self)
		shra.args = SubsObject(shra.args.subs+args.subs)
		return shra







class DualSubs(Tobj):
	def __init__(self,rows,pos=None):
		for sub in subs: assert type(sub) is TypeRow#safemode
		self.rows = rows
		transferlines(self,pos)


	def dpush(self,dsc,amt,lim,repls=None):
		left = 0
		cu = []
		for k in range(len(self.rows)):
			cu.append(self.rows[k].dpush(dsc+left,amt,lim,repls))
			left += longcount(self.rows[k].name)
		return DualSubs(cu)
	def compare(self,dsc,other,odsc=None,thot=None,extract=None):
		if type(other) is not DualSubs: return False
		if len(self.rows) != len(other.rows): return False
		left = 0
		for k in range(len(self.rows)):
			if not self.rows[k].compare(dsc+left,other.rows[k],odsc,thot,extract): return False
			left += longcount(self.rows[k].name)
		return True


	def unulimit(self,momin):
		tmomi = -1
		mopass = 0
		while mopass<=momin:
			tmomi += 1
			if self.rows[tmomi].obj == None: mopass += 1
		return tmomi


	def append(self,other):
		return DualSubs(self.rows+[other])
	def __add__(self,other):
		return DualSubs(self.rows+other.rows)
	def __len__(self):
		return len([k for k in self.rows if k.obj == None])
	def __getitem__(self, key):#must be verified first
		return [k for k in self.rows if k.obj == None][key].type

	def semavail(self,mog=None):
		if mog == None: mog = [j.name for j in self.rows]
		return [self.rows[j].type.semavail(mog[k]) if type(mog[k]) is list else mog[k] for k in range(len(self.rows)) if self.rows[j].obj == None]






	def iterfull(indesc,emptycallback,rerolling=False):
		class Convenience:
			def iterate(self2):
				for n in range(len(self.rows)):
					obj = self.rows[n].obj.verify(indesc.reroll() if rerolling else indesc) if self.rows[n].obj != None else emptycallback(n,self.rows[n],indesc)
					yield (n,indesc,self.rows[n],obj)
					indesc = indesc.addflat(self.rows[n].type.flatten(indesc.reroll() if rerolling else indesc,self.rows[n].name,obj=obj))
				self2.indesc = indesc
		return Convenience()

	def flatten(self,indesc,mog=None,assistmog=None,prep=None,obj=None,trim=False):
		def makepair(lim,mosh):
			if type(mosh) is not list: return (lim,lim+1)
			ysu = []
			for jk in mosh:
				nan,lim = makepair(lim,jk)
				ysu.append(nan)
			return (ysu,lim)
		if trim: mog = untrim(self,mog)
		if mog == None: mog = [k.name for k in self.rows]
		if assistmog == None:
			assistmog,ext = makepair(len(indesc),mog)
			indesc = indesc.postpush(ext,len(indesc))
		if type(mog) is not list: return super(Tobj,self).flatten(indesc,mog,assistmog,prep,obj)
		if type(obj) is SubsObject: assert len(obj.subs) == len(self)
		if type(obj) is Lambda and type(obj.obj) is SubsObject: assert len(obj.obj.subs) == len(self)
		assert len(self.rows) == len(mog)
		# if all(type(f.name) is str for f in self.rows) and all(type(f) is str for f in mog):
		# 	return [i for i in self[j].flatten(obj.subs[j].obj,limit,mog[j],prep) for j in range(len(mog))]
		s=-1
		def empopulate(n,row,indesc2):
			if obj == None: return row.type.emptyinst(len(indesc2),assistmog[n],prep=prep[0].emptyinst(len(indesc2)).subs)#prep is just the actual parameters that need to be prepended.
			s+=1
			if type(obj) is SubsObject: return obj.subs[s].dpush(None,len(indesc2)-len(indesc),len(indesc))
			if type(obj) is Lambda and obj.obj is SubsObject: return Lambda(obj.si,obj.obj.subs[s].dpush(None,len(indesc2)-len(indesc),len(indesc)),obj.sc)
			return RefTree(src=obj,name=s)
		cu = ScopeObject()
		for n,indesc,row,obj in self.iterfull(indesc,empopulate).iterate():
			cu = cu.addflat(row.type.flatten(indesc,mog[n],assistmog[n],prep,obj))
		return cu

	def emptyinst(self,limit,mog=None,prep=None):
		if mog == None: mog = striphuman(limit,[k.name for k in self.rows])
		if type(mog) is not list: return super(Tobj,self).emptyinst(limit,mog,prep)
		assert len(self.rows) == len(mog)
		mog = [mog[i] for i in range(len(mog)) if self.rows[i].obj == None]
		return SubsObject([self[k].emptyinst(limit,mog[k]) for k in range(len(self))])

	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assertstatequal(self,RefTree(),carry)
		outs = []
		for n in range(len(self.rows)):
			obj = self.rows[n].obj.verify(indesc) if self.rows[n].obj != None else None
			nty = self.rows[n].type.verify(indesc)
			outs.append(TypeRow(self.rows[n].name,nty,obj,self.rows[n].silent))
			indesc = indesc.addflat(nty.flatten(indesc.reroll(),self.rows[n].name,obj=obj))
		if then: return (DualSubs(outs,pos=self),indesc)
		if reqtype: return (DualSubs(outs,pos=self),RefTree())
		return DualSubs(outs,pos=self)


	def compactify(self,indesc,inyoks):
		return self.compacrecurse(self.compacassign(inyoks),[],indesc)

	def peelcompactify(self,indesc,compyoks,then=False,force=False,earlyabort=True):
		sbu = compyoks[0]
		mo = (self,)
		while True:
			ret = []
			mo = mo[0].compacrecurse(comp,[],[],indesc,retries=ret,force=force or compyoks[1],then=True,earlyabort=earlyabort)
			if mo == None: return None 
			earlyabort = False
			if len(ret) == 0:
				if then: return mo
				return mo[0]
			if [m[0] for m in sbu] == [m[0] for m in ret]: assert False
			sbu = ret




#it should still work because you typecheck every pass. youll just be catching it late potentially. (on something that was already verified; wtf)



	def compacassign(self,inyoks,overflow=None,safety=None):
		prev = False
		for g in inyoks:
			if g.name != None: prev = True
			elif prev: ErrorObject.fatal(self,"positional argument may not follow keyword argument.")
		def firstnamed(spoken,labels,car,mot=None):
			# more prots
			mot = [j.name for j in car.rows] if mot == None else mot
			for f in range(len(mot)):
				if car.rows[f].obj != None: continue
				if spoken[f] == True: continue
				if isinstance(mot[f],list):
					if spoken[f] == False: spoken[f] = [False]*len(mot[f])
					k = firstnamed(spoken[f],labels,car.rows[f].type,mot[f])
					if k: return [f] + k
				elif mot[f] == labels[0] or (labels[0] == None and not car.rows[f].silent.question):
					if len(labels) == 1:
						spoken[f] = True
						return [f]
					nxc = car.rows[f].type.type if type(car.rows[f].type) is Strategy else car.rows[f].type
					if spoken[f] == False: spoken[f] = [False]*len(nxc)
					k = firstnamed(spoken[f],labels[1:],nxc)
					if k: return [f]+k
		def fullp(spoken):
			return spoken == True or all(fullp(k) for k in spoken)
		spoken = [False]*len(self.rows)
		yoks = []
		for s in range(len(inyoks)):
			nan = firstnamed(spoken,inyoks[s][0],self)
			if nan == None:
				if safety != None and s < safety: return None
				overflow.append(inyoks[s])
			else: yoks.append((nan,inyoks[s][1],inyoks[s][2]))
		return (yoks,fullp(spoken))



	def compacrecurse(self,yoks,trail,prep,indesc,retries=None,force=False,then=False,earlyabort=False):
		def fillempty(n,row,indesc):
			thot = prep+namerical(len(indesc),[k.name for k in self.rows[:n]],[])
			lentotal = len(indesc)
			lentho = len(thot)
			lencom1 = lentotal - lentho
			for k in yoks:
				if k[0] == trail+[n]:
					if k[2] != False:
						if not row.compare(lentotal,k[2].dpush(lentho,lencom1),lentotal,thot,retries):
							if earlyabort: return None
							assert False
						return d[2].dpush(None,lentho,lencom1)
					if earlyabort:
						retries.append(k)
						return None
					if type(k[1]) is Lambda and not k[1].obj.needscarry() and type(row) is Strategy and len(row.args) == len(k[1].si):
						try:
							yasat = row.args.dpush(None,-lentho,lencom1)
						except DpushError: pass
						else:
							nobj,ntyp = k[1].obj.verify(indesc.trimabsolute(len(prep)).addflat(yasat.flatten(indesc,k[1].si,trim=True)),reqtype=True)
							if not row.compare(lentotal,ntyp.dpush(lentho,lencom1),lentotal,thot,retries): assert False
							return nobj.dpush(None,lentho,lencom1)
					try: row.dpush(None,-lentho,lencom1)
					except DpushError:
						if not force:
							retries.append(k)
							return
					return obj.verify(indesc.prepush(lentho,lencom1),row)

		def namerical(lim,names,sof):
			if type(names) is not list: return (lim,sof)
			i = []
			for j in range(len(names)):
				i = i+namerical(lim+len(i),names[j],sof+[j])
			return i
		cu = []
		conven = self.iterfull(indesc,fillempty,rerolling=True)
		for n,indesc,row,obj in conven.iterate():
			if any(len(o.trail)>len(trail)+1 and o.trail[:len(trail)+1] == trail+[n]):
				thot = prep+namerical(len(indesc),[k.name for k in self.rows[:n]],trail)
				moro = row.compacrecurse(yoks,trail+[n],thot,indesc,retries=retries,force=force,earlyabort=earlyabort)
				if moro == None: return None
				obj = row.obj if row.obj != None else SubsObject() if moro.isemptytype() else None
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				obj = row.obj.verify(indesc.reroll()) if row.obj != None else obj if obj != None else None
				cu.append(TypeRow(row.name,row.verify(indesc.reroll()),obj,self.rows[n].silent))
		if then: return (DualSubs(cu),conven.indesc)
		return DualSubs(cu)


class SubsObject(Tobj):
	def __init__(self,subs,pos=None):
		for sub in subs: assert type(sub) is SubRow#safemode
		self.subs = subs
		transferlines(self,pos)




	def dpush(self,dsc,amt,lim,repls=None):
		return SubsObject([k.dpush(dsc,amt,lim,repls) for k in self.subs],self)
	def compare(self,dsc,other,odsc=None,thot=None,extract=None):
		if type(other) is not SubsObject: return False
		if len(self.subs) != len(other.subs): return False
		return all(self.subs[k].compare(dsc,other.subs[k],odsc,thot,extract) for k in range(len(self.subs)))




	def phase1(self,indesc):
		return [(s.name,(s.obj,False)) if s.needscarry() else (s.name,s.verify(indesc,reqtype=True)) for s in self.subs]
	def phase1_gentle(self):
		for s in self.subs: assert s.name == None
		return [(None,(s.obj,True)) for s in self.subs]
	def needscarry(self):
		return True
	def verify(self,indesc,carry=None):
		assert type(carry) is DualSubs
		st = carry.compactify(indesc,self.phase1(indesc)).rows
		for j in st: assert j.obj != None
		cuu = []
		left = 0
		for g in range(len(st)):
			if carry.rows[g].obj == None:
				cuu.append(SubRow(None,st[g].obj.dpush(-left,len(indesc))))
			left += longcount(carry.rows[g].name)
		return SubsObject(cuu)
class TemplateUse(Tobj):
	def __init__(self,obj,subs,pos=None):
		assert type(subs) is SubsObject
		transferlines(self,pos)
	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False):
		res = self.obj.verify(indesc,RefTree())
		assert type(res) is DualSubs
		sob = res.compactify(indesc,carry.phase1(indesc))
		if reqtype: (sob,RefTree())
		return sob
class Lambda(Tobj):
	def __init__(self,si,obj,sc=None,pos=None):
		# assert type(si) is ScopeIntroducer or type(si) is DualSubs
		self.si = si
		self.obj = obj
		self.sc = sc
		transferlines(self,pos)

	def dpush(self,dsc,amt,lim,repls=None):
		return Lambda(self.si,self.obj.dpush(dsc+self.sc,amt,lim,repls),self.sc,self)
	def compare(self,dsc,other,odsc=None,thot=None,extract=None):
		if type(other) is not Lambda: return False
		def conservative(a,b):
			if type(a) is list:
				if type(b) is not list: return False
				if len(a) != len(b): return False
				return all(conservative(a[c],b[c]) for c in range(len(a)))
			return type(b) is not list
		assert self.sc == other.sc
		return conservative(self.si,other.si) and self.obj.compare(dsc+self.sc,other.obj,odsc,thot,extract)


	def needscarry(self):
		if len(self.si) == 0: return self.obj.needscarry()
		return True

	def verify(self,indesc,carry=None,reqtype=False):
		if len(self.si) == 0: return self.obj.verify(indesc,carry,reqtype)
		if carry==None: ErrorObject.fatal(self,"type of arguments could not be inferred.")
		if type(carry) is not Strategy: ErrorObject.fatal(self,"lambda provided to non-lambda type.")
		if len(self.si) > len(carry.args): ErrorObject.fatal(self,"too many lambda arguments provided.")
		tmomi = carry.args.unulimit(len(self.si))
		truncargs = DualSubs(carry.args.rows[:tmomi])
		ntype = Strategy(DualSubs(carry.args.rows[tmomi:]),carry.type)
		fid = self.obj.verify(indesc.addflat(truncargs.flatten(indesc.reroll(),self.si,trim=True)),ntype)
		allpassalong = truncargs.emptyinst(len(indesc),striphuman(untrim(self.si)))
		elim = 0
		if type(fid) is RefTree:
			nks = copy.copy(fid.args.subs)
			while elim<len(allpassalong.subs) and len(nks):
				if not nks[-1].compare(None,allpassalong.subs[len(allpassalong.subs)-1-elim]): break
				elim+=1
				nks = nks[:-1]
			fid = copy.copy(fid)
			fid.args = SubsObject(nks)
		if len(self.si) == elim: return fid
		return Lambda(self.si[:len(self.si)-elim],fid,longcount(truncargs),pos=self)

	def claimlambda(self,indesc,tyargs,args):
		momin = min(len(self.si),len(args))
		tmomi = tyargs.args.unulimit(momin)
		brac = DualSubs(tyargs.args.rows[:tmomi])
		brac1 = DualSubs(tyargs.args.rows[tmomi:])
		sard = indesc.addflat(brac.flatten(self.si[:momin],trim=True,obj=SubsObject(args.subs[:momin]))).postpush(-trimlongcount(brac,trim),len(indesc))
		if len(args)>len(self.si):
			return self.obj.claimlambda(sard,brac1,SubsObject(args.subs[momin:]))
		gogra = self.obj.verify(sard,tyargs.type.verify(sard))
		if len(args)<len(self.si):
			return Lambda(self.si[momin:],gogra)
		return gogra


	def addlambdas(self,args):
		if len(args) == 0: return self
		return Lambda(self.si+args.semavail(),self.obj,None if self.sc == None else self.sc+longcount([k.name for k in args.rows]),pos=self)





need to reimplement sc...
each Lambda construction.




class Strategy(Tobj):
	def __init__(self,args=None,type=None,pos=None):
		if type(name) is ScopeIntroducer: name = name.dat
		self.args = DualSubs(pos=pos) if args == None else args
		self.type = type
		transferlines(self,pos)
		# assert type(self.args) is DualSubs#safemode





	def dpush(self,dsc,amt,lim,repls=None):
		return Strategy(self.args.dpush(dsc,amt,lim,repls),self.type.dpush(dsc+longcount(self.args),amt,lim,repls),self)
	def compare(self,dsc,other,odsc=None,thot=None,extract=None):
		if type(other) is not Strategy: return False
		return self.args.compare(dsc,other.args,odsc,thot,extract) and self.type.compare(dsc+longcount(self.args),other.type,odsc,thot,extract)



	def addfibration(self,args):
		return Strategy(self.args+args,self.type,pos=self)


	def semavail(self,mog):
		return self.type.semavail(mog)

	def emptyinst(self,limit,mog,prep=None):
		if prep == None: prep = SubsObject()
		return self.type.emptyinst(limit,mog,prep + self.args.emptyinst(limit))


	def flatten(self,indesc,mog=None,assistmog=None,prep=None,obj=None,trim=False):
		if obj != None: obj = obj.claimlambda(indesc.reroll(),self.args,self.args.emptyinst(len(indesc)))
		arp = self.args.verify(indesc)
		njprep = (arp,len(indesc)) if prep == None else (prep[0].dpush(None,len(indesc)-prep[1],prep[1])+arp,len(indesc))


		return self.type.flatten(indesc.addflat(self.args.flatten(indesc)),mog,assistmog,njprep,obj,trim)



	def needscarry(self):
		if len(self.args) == 0: return self.type.needscarry()
		return False
	@debugdebug
	def verify(self,indesc,carry=None,reqtype=False):
		verargs,indesc = self.args.verify(indesc,then=True)
		if len(verargs) == 0: return self.type.verify(indesc,carry,reqtype=reqtype)
		assertstatequal(self,RefTree(),carry)
		vertype = self.type.verify(indesc,RefTree())
		if type(vertype) is Strategy:
			verargs = verargs + vertype.args
			vertype = vertype.type
		if reqtype: return (Strategy(args=verargs,type=vertype,pos=self),RefTree())
		return Strategy(args=verargs,type=vertype,pos=self)




make sure no emptyinst is called when trim is expected.

review compactify's overflow protocol-> compare itself checks that its not overriding none, so en\sure that that is respected.

make sure all uses of flatten (outside of flatten itself) respect the whole obj-is-in-output-space proclamation.


class RefTree(Tobj):
	def __init__(self,name=None,args=None,src=None,safety=None,pos=None):
		self.name   = 0 if name == None else name
		self.args   = SubsObject(pos=pos) if args == None else args
		self.src    = src
		self.safety = safety
		transferlines(self,pos)

	def dpush(self,dsc,amt,lim,repls=None):
		gy = self.name
		if gy >= lim and self.src == None:
			gy -= amt
			if gy < lim:
				if repls == None: return None
				for j in repls:
					fom = self.dpush(dsc,lim-amt-len(repls)-dsc,lim-amt-len(repls))
					if fom == None: continue
					if fom.compare(dsc,j[0]): return j[1]
				return None
		return RefTree(gy,self.args.dpush(dsc,amt,lim,repls),None if self.src == None else self.src.dpush(dsc,amt,lim,repls),self)


	def compare(self,dsc,other,odsc=None,thot=None,extract=None):
		if type(other) is not Strategy: return False
		if self.src != None:
			if other.src == None or not self.src.compare(amt,lim,other.src,thot,extract): return False
		elif thot != None:
			for k in thot:
				if k[0] == self.name:
					for j in extract:
						if j[0] == k[1] and j[2] == False: return True
					repls = []
					valid = True
					for g1 in range(len(other.args.subs)):
						if type(other.args.subs[g1]) is not RefTree or other.args.subs[g1].name<odsc:
							valid = False
							break
						for g2 in range(g1):
							if other.args.subs[g1].compare(dsc,other.args.subs[g2]):
								valid = False
								break
						if not valid: break
					if not valid: break
					gr = other.dpush(dsc,odsc+len(repls)-dsc,odsc,repls=repls)
					mod = gr if len(repls) == 0 else Lambda(["_"]*len(repls),gr)
					if len(repls) == 0: return gr
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(0,mod):
					extract.append((k[1],mod,True))
					return True
		return self.name == other.name and self.args.compare(amt,lim,other.args,thot,extract)




	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False):

		if hasattr(self,'foclnsafety'): assert self.foclnsafety == indesc.beginlen()#safemode


		if self.src == None:
			tra = indesc.symextract(self.name,self.subs.phase1(),reqtype=reqtype,safety=self.safety)
			if tra != None: return tra
			assert False
		else:
			orig = src.verify(self,indesc,reqtype=True)
			p1 = self.subs.phase1()
			if type(orig[1]) is DualSubs:
				tra = orig[1].flatten(indesc,obj=orig[0]).symextract(self.name,p1,reqtype=reqtype,safety=self.safety)
				if tra != None: return tra
			if type(orig[0]) is RefTree and orig[0].src == None:
				tra = indesc.symextract(orig[0].name+"."+self.name,orig[0].args.phase1_gentle()+p1,reqtype=reqtype,safety=self.safety)
				if tra != None: return tra
			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,safety=self.safety)
			if tra != None: return tra
			assert False





class OperatorSet(Tobj):
	def __init__(self,array,pos):
		self.array = array
		transferlines(self,pos)
	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False):
		fulltree = []
		insert = fulltree
		for ind in self.array:
			if type(ind) is str:
				if insert == None:
					prec = indesc.binary_precidence(ind)
					shift = fulltree
					while len(type(shift[-1])) == 3 and shift[-1][1] < prec:
						shift = shift[-1][2]
					shift[-1] = (ind,prec,[shift[-1]])
					insert = shift[-1][2]
				else:
					urnary = (ind,indesc.urnary_precidence(ind),[])
					insert.append(urnary)
					insert = urnary[2]
			else:
				insert.append(ind.verify(indesc,reqtype=True))
				insert = None
		def douparse(tree):
			if len(tree) == 2: return tree
			return indesc.symextract(tree[0],[(None,douparse(u)) for u in tree[2]],reqtype=True,safety=len(tree[2]))
		if reqtype: return douparse(fulltree[0])
		return douparse(fulltree[0])




	DSC CANNOT BE NONE


comparing dualsubs needs to be much much better.

dualsubs objs never get compared, also remove typerow compare function entirely.


	completely separate mappings for what is considered equal... need to keep track of some sort of push objects.

	then when you are comparing to extract something... it just goes back to odsc anyway, so you dont have to worry about the pushes.





# game(animation editor)
# hackathon
# this

# minecraft server
# hackathon(eric)


#bring back pos system and get better error tracking.


# push some of the verification to instantiation: a.b must share the same first parameters as a .


 # have multiple channels for refferring back to a specific caller.




#list of mangles:
#mangle 1: de morgan negation buitin
#mangle 2: compact variables (tracked through attached object.)
#mangle 3: when type is Strategy<DualSubs>, wrap self in singleton to try to match it.
	#applies to symextract and lambda
	#when too many lambda arguments are provided, the remainder is wrapped in a singleton and the match is attempted.
#mangle 4: when type is equality in space of DualSubs, accept tuple of equalities.
#mangle 5: when type is [k:K]P and you provide P it should just assume constant.










