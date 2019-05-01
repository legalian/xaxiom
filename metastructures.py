
from .structures import *
# from inspect import getframeinfo, stack


class ObjKind:
	def refsany(self,si):
		def minjcontains(j):
			if isinstance(j,list):
				return any(minjcontains(o) for o in j)
			return self.refs(j)
		return minjcontains(si.dat)



def parsesubsfromsrc(parsed):
	if parsed.data == 'objargumentseries':
		jarf = []
		for k in range(len(parsed.children)):
			jarf.append(IndividualSub(None,ScopeIntroducer(parsed.children[k].children[:-1]),parsed.children[k].children[-1],[]))
		return SubsObject(jarf)
	if parsed.data == 'objargumentnamedseries':
		ij = []
		for n in range(len(parsed.children)):
			m = parsed.children[n]
			if len(m.children) == 1 and type(m.children[0]) is str:continue
			moch = m.children[0 if len(m.children)==1 else 1]
			nname = m.children[0] if len(m.children)==2 else None

			nsi  = moch.children[:-1]
			nobj = moch.children[-1]
			nbon = [s.children[0] for s in parsed.children[:n] if type(s.children[0]) is str]
			ij.append(IndividualSub(nname,ScopeIntroducer(nsi),nobj,nbon))
		return SubsObject(ij)
	assert False


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





fonocolls = 0
fonodepth = 0



def debugdebug(F):
	# return F
	def wrapper(*args,**kwargs):
		global fonocolls
		global fonodepth
		try:
			fonocolls += 1
			if fonocolls == 500000: assert False
			janh = F.__name__
			# if janh != "substitute" and janh != "subsmake":
			# 	print("\t"*fonodepth+"entering: ",type(args[0]).__name__+"."+janh)
			# fonodepth += 1
			ahjs = F(*args,**kwargs)
			# fonodepth -= 1

			if janh == "verify":
				if not ahjs.verified:
					print("error on: ",type(args[0]).__name__+"."+janh)
					assert ahjs.verified


			if janh == "substitute":
				if args[0].verified and len(args[2]) == 0 and not ahjs.verified:
					print("error on: ",type(args[0]).__name__+"."+janh)
					assert False




			return ahjs
		except ErrorObject as u:
			relevant = type(args[0]).__name__+"."+F.__name__
			iswide = callable(getattr(args[0], "wide_repr", None))
			strin = args[0].wide_repr(0) if iswide else str(args[0])
			print("-traceback: "+relevant+" -->",strin)
			raise u
	return wrapper
def mapping(subsf,subso,errors):
	construct = [None for n in subso]
	sht1 = 0
	sht2 = 0
	snarg = []
	for g in subsf:
		if g.name == None: continue
		if g.name in snarg: raise errors.error("Duplicate keyword arguments are not allowed.")
		snarg.append(g.name)

	for aj in range(len(subsf)):
		if subsf[aj].name == None:
			found = False
			for ja in range(sht1,len(subso)):
				if subso[ja].name == None:
					sht1 = ja+1
					construct[ja] = aj
					found = True
					break
			if not found:
				for ja in range(sht2,len(subso)):
					if subso[ja].name != None:
						sht2 = ja+1
						construct[ja] = aj
						found = True
						break
			if not found:
				raise errors.error("Too many positional arguments.")
	for aj in range(len(subsf)):
		if subsf[aj].name != None:
			found = False
			for ja in range(sht2,len(subso)):
				if subso[ja].name == subsf[aj].name:
					sht1 = ja
					construct[ja] = aj
					found = True
					break
			if not found:
				for ja in range(sht2):
					if subso[ja].name == subsf[aj].name:
						raise errors.error("Parameter specified twice:" + subsf[aj].name)
				raise errors.error("Unrecognized named parameter:" + subsf[aj].name)
	return construct


@debugdebug
def subsmake(lvluprow,mog,errors):
	def internalsubsmake(lvluprow,mog,trail):
		if isinstance(lvluprow,list):
			resk = []
			for f in range(len(lvluprow)):
				resk = resk + internalsubsmake(lvluprow[f],mog,trail+[f])
			return resk
		jog = mog.obj
		for s in trail:
			jog = ObjKindReferenceTree(src=jog,name=s)
		return [IndividualSub(lvluprow,mog.si,jog,[])]
	if type(lvluprow) is ScopeIntroducer: lvluprow = lvluprow.dat
	assert type(errors) is ErrorObject and isinstance(lvluprow,list)
	if len(lvluprow) != len(mog):
		raise errors.error("mechanical: Wrong number of introduced parameters.")
	resk = []
	for f in range(len(lvluprow)):
		if isinstance(lvluprow[f],list):
			if len(mog.subs[f].si) != 0:
				raise errors.error("Mechanical error: Function-to-tuple unwrapping is not supported.")
			if type(mog.subs[f].obj) is not ObjKindUnionSet:
				resk = resk + internalsubsmake(lvluprow[f],mog.subs[f],[])
			else:
				resk = resk + subsmake(lvluprow[f],mog.subs[f].obj.subs,errors)
		else:
			resk.append(IndividualSub(lvluprow[f],mog.subs[f].si,mog.subs[f].obj,[]))
	return resk
def meagersinglename(forbidden,intr,*repl):
	if intr == None: return
	if type(forbidden) is dict:
		forbidden = [v for k,v in forbidden.items() if k!=intr]
	assert type(intr) is str
	if not any(o.refs(intr) for o in repl) and intr not in forbidden: return intr
	g = intr.split("$")
	assert len(g) == 1 or len(g) == 2
	n = int(g[1]) if len(g) == 2 else 1
	h = g[0]
	while any(o.refs(h+"$"+str(n)) for o in repl) or h+"$"+str(n) in forbidden: n+=1
	return h+"$"+str(n)
def mostmeagername(exrevf,intrs,repl):
	assert type(exrevf) is RenamerObject
	assert type(intrs)  is ScopeIntroducer
	repls = copy.copy(exrevf.data)
	for intr in intrs.allvars():
		z = meagersinglename(repls,intr,repl)
		if z == intr or z == None: continue
		repls[intr] = z
	return RenamerObject(repls)







class RenamerObject:
	def __init__(self,data=None,alt=None):
		self.data = data if data != None else {}
		self.alt = alt if alt != None else {}
		assert type(self.data) is dict
		assert type(self.alt) is dict
	def without(self,si):
		return RenamerObject({key:data for (key,data) in self.data.items() if not si.contains(key)},self.alt)
	def alternate(self):
		return RenamerObject(self.alt,self.data)
	def only(self,si):
		return RenamerObject({key:data for (key,data) in self.data.items() if si.contains(key)},self.alt)
	def __getitem__(self,key):
		return self.data.get(key,key)
class ScopeSelectionObject:
	def __init__(self,data=None):
		self.data = []
		if data != None:
			for j in data:
				if isinstance(j,str):
					self.data.append((j,j))
				else:
					self.data.append(j)
	def introducer(self):
		return ScopeIntroducer([p[1] for p in self.data])
	def upperintroducer(self):
		return ScopeIntroducer([p[0] for p in self.data])
	def without(self,subs):
		return ScopeSelectionObject([p for p in self.data if p[0] not in [i.name for i in subs.subs]])
	def rename(self,revf):
		return ScopeSelectionObject([(p[0],revf[p[1]]) for p in self.data])
	def upperrename(self,revf):
		return ScopeSelectionObject([(revf[p[0]],p[1]) for p in self.data])
	def bon(self):
		return [p[0] for p in self.data]
	def asrenamer(self):
		return RenamerObject(dict(self.data))
	def __getitem__(self,key):
		return self.asrenamer()[key]
	def __len__(self):
		return len(self.data)
	def __repr__(self):
		return "["+",".join([y[0]+":"+y[1] for y in self.data])+"]"
	def __eq__(self,other):
		if type(other) is not ScopeSelectionObject: return False
		return self.data == other.data
class CrossNameObject:
	def __init__(self,data=None):
		self.data = [] if data == None else data
	def sertequiv(self,a,b):
		zar = a.paired(b)
		if zar == None: return
		return CrossNameObject(self.data+zar)
	def equivalen(self,a,b):
		for j in reversed(self.data):
			if j[0]==a or j[1] == b:
				return j[0] == a and j[1] == b
		return a==b
class ErrorObject(BaseException):
	def __init__(self,rer=None,tac=None):
		self.rer = [] if rer == None else rer
		self.tac = [] if tac == None else tac
		self.blame = None
	def takeblame(self,obk):
		self.blame = obk
	def nonfatal(self,err,obk=None):
		assert type(err) is str
		if obk == None:
			assert self.blame != None
			self.rer.append((err,self.blame,self.tac))
		else:
			self.rer.append((err,obk,self.tac))
	def error(self,err,obk=None):
		# assert False
		assert type(err) is str
		if obk == None:
			assert self.blame != None
			return ErrorObject([(err,self.blame,self.tac)])
		else:
			return ErrorObject([(err,obk,self.tac)])
	def tack(self):
		assert self.blame != None
		return ErrorObject(self.rer,self.tac+[self.blame])
	def reports(self,window):
		errors = list(dict.fromkeys([(o[0],o[1].row,o[1].column) for o in self.rer]))
		phantoms = []
		for erroro in errors:
			error = '<span style="color:pink">█'+erroro[0].replace('>','&gt;').replace('<','&lt;')+'</span>'
			pos = window.view.text_point(erroro[1],erroro[2])
			phantoms.append(sublime.Phantom(
				sublime.Region(pos,pos+4),
				error,
				sublime.LAYOUT_BELOW
			))
		return phantoms
	def __str__(self):
		if len(self.rer) == 1:
			o=self.rer[0]
			return str((o[0],o[1].row,o[1].column))
		return "multiple errors"
class ScopeIntroducer:
	def __init__(self,dat):
		self.dat = dat
	def __repr__(self):
		def pretty(j):
			if isinstance(j,list): return "("+",".join([pretty(i) for i in j])+")"
			return str(j)
		if len(self.dat) == 0: return ""
		return "["+",".join([pretty(i) for i in self.dat])+"]"

	def paired(self,other):
		def croc(a,b):
			if isinstance(a,list) and isinstance(b,list):
				if len(a) != len(b): return None
				fo = []
				for i in range(len(a)):
					ui = croc(a[i],b[i])
					if ui == None: return None
					fo = fo + ui
				return fo
			if isinstance(a,list) or isinstance(b,list): return None
			return [(a,b)]
		return croc(self.dat,other.dat)

	def contains(self,label):
		if label == None: return False
		assert type(label) is str
		def contains(lvluprow):
			for h in lvluprow:
				if h == label: return True
				if isinstance(h,list) and contains(h): return True
			return False
		return contains(self.dat)
	def rename(self,revf):
		def ren(ju):
			if isinstance(ju,list):
				return [ren(i) for i in ju]
			return revf[ju]
		return ScopeIntroducer(ren(self.dat))
	def allvars(self):
		def ren(ju):
			if isinstance(ju,list):
				return [g for i in ju for g in ren(i)]
			return [ju]
		return ren(self.dat)
	def __len__(self):
		return len(self.dat)
	def __eq__(self,other):
		if type(other) is not ScopeIntroducer: return False
		return self.dat == other.dat






#-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=







class IndividualSub:
	def __init__(self,name,si,obj,bon,expected=None,exverified=False,extypeverified=False):
		assert type(name) is str or name == None
		assert type(si) is ScopeIntroducer
		assert issubclass(type(obj),ObjKind)

		self.linnonono = None#getframeinfo(stack()[1][0]).lineno

		self.name = name
		self.si = si
		self.obj = obj
		self.bon = bon if type(bon) is ScopeSelectionObject else ScopeSelectionObject(bon)
		self.expected = expected

		self.easyverified = exverified and self.obj.verified
		self.verified = extypeverified and (self.expected != None and self.expected.verified) and self.obj.verified
	def __repr__(self):
		res = ""
		if self.name != None: res = res+self.name+"="
		if len(self.bon) != 0: res = res+str(self.bon)+"|"
		res = res+str(self.si)+str(self.obj)
		return res
	def wide_repr(self,depth):
		res = ""
		if self.name != None: res = res+self.name+"="
		if self.expected != None: res = res+"!"
		if len(self.bon) != 0: res = res+str(self.bon)+"|"
		res = res+str(self.si)+self.obj.wide_repr(depth)
		return res
	@debugdebug
	def substitute(self,revf,repl,errors):#,replacebon=False
		mmn = mostmeagername(revf,self.bon.introducer(),repl)
		mmn2 = mostmeagername(mmn,self.si,repl)
		uhf = self.obj.substitute(mmn2,repl.without(self.bon.introducer()).without(self.si),errors)

		nbon = self.bon.rename(mmn)
		# nname = self.name
		# if replacebon:
		# 	nbon = nbon.upperrename(revf)
		# 	nname = revf[nname]

		# 	revf = RenamerObject()
		# 	repl nee

		jae = None if self.expected == None else self.expected.substitute(revf,repl,errors)

		sgo = IndividualSub(self.name,self.si.rename(mmn2),uhf,nbon,jae,exverified=self.easyverified,extypeverified=self.verified)
		sgo.linnonono = self.linnonono
		return sgo

	def replacebon(self,revf):
		nbon = self.bon.upperrename(revf)
		return IndividualSub(revf[self.name],self.si,self.obj,nbon,self.expected,exverified=self.easyverified,extypeverified=self.verified)



	@debugdebug
	def compactify(self,repl,errors):
		uew = []
		for r in repl.subs:
			jambo = [d for d in r.bon.bon() if d not in self.bon.bon()]
			mmn = mostmeagername(RenamerObject(),ScopeIntroducer(jambo),self.obj)
			nbon = r.bon.rename(mmn)
			nobj = r.obj.substitute(mmn.without(r.si),SubsObject(),None)
			uew.append(IndividualSub(r.name,r.si,nobj,nbon))
		nsubs = SubsObject(uew)
		mmn = mostmeagername(RenamerObject(),self.bon.introducer(),repl)
		mmn2 = mostmeagername(mmn,self.si,repl)
		# jae = None if self.expected == None else self.expected.substitute(RenamerObject(),nsubs.only(self.bon.upperintroducer()),errors)
		# jae = "now "
		# jae = None if self.expected == None else "now this some horseshit"
		uhf = self.obj.substitute(mmn2,nsubs.redirect(self.bon).without(self.si),errors)
		return IndividualSub(self.name,self.si.rename(mmn2),uhf,self.bon.without(nsubs).rename(mmn2),exverified=self.easyverified)
	@debugdebug
	def preverify(self,scope,shah,zaku,errors):
		if self.easyverified:
			return (self.si,self.obj)
		assert scope.verified
		shama = StratSeries(copy.copy(scope.data),exverified=True)
		assert shama.verified

		mmnstrat = RenamerObject()
		mmnobj = RenamerObject()

		for h in range(len(shah)):
			mn = meagersinglename([f.name for f in shama.data],shah[h].name)

			for y in self.bon.data:
				if shah[h].name == y[0]:
					mmnobj.data[y[1]] = mn
					break
			

			zxc = copy.copy(shah[h].substitute(mmnstrat,SubsObject(),None))
			zxc.name = mn
			mmnstrat.data[shah[h].name] = mn
			shama.data.append(zxc)

		zaku = zaku.substitute(mmnstrat,SubsObject(),None)


		zakummn = mostmeagername(mmnobj,self.si,zaku)
		nssi = self.si.rename(zakummn)
		shse = self.obj.substitute(zakummn,SubsObject(),None)
		zaku = zaku.reformat(shama,nssi,errors)
		shse = shse.verify(shama+zaku.args,zaku.type,errors)

		return (nssi,shse)
	def refs(self,label):
		label = self.bon[label]
		if self.si.contains(label): return False
		return self.obj.refs(label)
	def equate(self,cno,other):
		con = cno.sertequiv(self.si,other.si)
		if con == None: return False
		return self.obj.equate(con,other.obj)
class SubsObject:
	def __init__(self,data=None,exverified=False):
		if data != None:
			for k in data: assert type(k) is IndividualSub
		self.subs = [] if data == None else data
		self.verified = (exverified and all(i.verified for i in self.subs)) or self.subs == []

	def __repr__(self):
		return ",".join([str(k) for k in self.subs])
	def wide_repr(self,depth):
		sep = "\n"+"\t"*depth
		return sep+(","+sep).join([k.wide_repr(depth+1) for k in self.subs])
	def oblong_repr(self,depth):
		return ",".join([k.wide_repr(depth) for k in self.subs])

	@debugdebug
	def substitute(self,revf,repl,errors):
		return SubsObject([i.substitute(revf,repl,errors) for i in self.subs],exverified=self.verified)
	def replacebon(self,revf):
		return SubsObject([i.replacebon(revf) for i in self.subs],exverified=self.verified)
	# @debugdebug
	# def compactify(self,repl,errors):
	# 	return SubsObject([i.compactify(repl,errors) for i in self.subs],exverified=self.verified)
	def without(self,so):
		return SubsObject([d for d in self.subs if not so.contains(d.name)],exverified=self.verified)
	def only(self,so):
		return SubsObject([d for d in self.subs if so.contains(d.name)],exverified=self.verified)
	def refs(self,label):
		return any(i.refs(label) for i in self.subs)
	def get(self,label):
		if type(label) is int:
			if label>=len(self.subs): return None
			return self.subs[label]
		for t in reversed(self.subs):
			if t.name == label:
				return t
		return None
	def redirect(self,a):
		assert type(a) is ScopeSelectionObject
		nrepl = []
		for i in self.subs:
			marm = copy.copy(i)
			for pair in a.data:
				if marm.name == pair[0]:
					marm.name = pair[1]
					nrepl.append(marm)
					break
		return SubsObject(nrepl)


	@debugdebug
	def precompact(self,scope,cars,errors,onlycomplete=False,argmode=False):
		# print("clowning: ",len(self.subs))
		assert type(scope) is StratSeries
		assert type(cars) is StratSeries
		assert type(errors) is ErrorObject
		if argmode:
			if len(self.subs) != len(cars): raise errors.error("Illegal argument count.")
			gar = range(len(self.subs))
		else:
			gar = mapping(self.subs,cars,errors)
		simpsubs = []
		pospsubs = []
		zn = []
		mmn = RenamerObject()
		fahg = []

		carscope = scope

		for i in cars.data:
			assert i.verified

		for z in range(len(gar)):
			zaku = cars[z].substitute(mmn,SubsObject(),None)
			zaku = zaku.substitute(RenamerObject(),SubsObject(simpsubs),errors)
			zaku = zaku.verify(scope+StratSeries([zn[i] for i in range(z) if gar[i] == None]),errors.tack())
			faku = zaku
			if gar[z] == None:
				if not onlycomplete:
					mmn = mostmeagername(mmn,ScopeIntroducer([cars[z].name]),SubsObject(simpsubs))
					fahg.append((cars[z].name,mmn[cars[z].name]))
					zaku.name = mmn[zaku.name]
					zn.append(zaku)
					continue
				if cars[z].name == None: raise errors.error("Not enough positional arguments.")
				else: raise errors.error("Missing named argument:"+cars[z].name)
			for check in self.subs[gar[z]].bon.bon():
				if check not in [cars[k].name for k in range(z)] and self.subs[gar[z]].obj.refs(check) and not self.subs[gar[z]].si.contains(check):
					if check in [cars[k].name for k in range(z,len(gar))]:
						raise errors.error("This variable usage violates well-ordering property: "+check)
					else:
						raise errors.error("Mechanical error: referenced bon which isn't in given type list: "+check)
			

			# evenbother = False
			jambo = []#jambo is going to be different
			for h in range(z):
				if gar[h] == None:
					for y in self.subs[gar[z]].bon.data:
						if zn[h].name == y[0]:
							if self.subs[gar[z]].obj.refs(y[1]) and not self.subs[gar[z]].si.contains(y[1]):
								jambo.append(mmn[y])
							break
				# else:
				# 	evenbother = True

			# recombine = self.subs[gar[z]].substitute(mmn,SubsObject(),None,replacebon=True)
			recombine = self.subs[gar[z]].replacebon(mmn)

			# if evenbother:
				# silencer = ErrorObject()
				# silencer.takeblame(errors.blame)

				#fix this- switch to silencer
				#evenbother is broke...



			# koso = recombine.preverify(scope,zn,zaku,errors)#doesnt use or provide name
			# recombine = IndividualSub(cars[z].name,koso[0],koso[1],recombine.bon,exverified=True)




			koso = recombine.compactify(SubsObject(simpsubs),errors)

			# print("()()()()()",koso)
			koso = koso.preverify(scope,[zn[h] for h in range(z) if gar[h] == None],zaku,errors.tack())

			# else:
			# 	koso = presco.preverify(scope,zn,zaku,errors)

			simpsubs.append(IndividualSub(None,koso[0],koso[1],jambo,faku,exverified=True,extypeverified=True))
			mmn = mostmeagername(mmn,ScopeIntroducer([cars[z].name]),SubsObject(simpsubs))
			simpsubs[-1].name = mmn[cars[z].name]
			fahg.append((cars[z].name,mmn[cars[z].name]))

			zaku.name = mmn[zaku.name]
			zn.append(zaku)
		# assert False
		fomo = DualSubs(StratSeries(zn,exverified=True),SubsObject(simpsubs,exverified=True),ScopeSelectionObject(fahg),exverified=True)
		for j in simpsubs:
			assert j.verified

		for z in zn:
			assert z.verified

		assert fomo.variables.verified
		assert fomo.subs.verified
		assert fomo.verified

		fomo.availvariables()
		return fomo
	def __len__(self):
		return len(self.subs)
	def equate(self,cno,other):
		if len(self) != len(other): return False
		ja = [False]*len(self)
		jb = [False]*len(self)
		for a in range(len(self)):
			if self.subs[a].name == None: continue
			for b in range(len(self)):
				if self.subs[a].name == other.subs[b].name:
					if not self.subs[a].equate(cno,other.subs[b]): return False
					ja[a] = True
					jb[b] = True
					break
		b=0
		for a in range(len(self)):
			if ja[a]: continue
			while jb[b]: b+=1
			if not self.subs[a].equate(cno,other.subs[b]): return False
		return True
class StratSeries:
	def __init__(self,data=None,exverified=False):
		self.data = [] if data == None else data
		for k in self.data: assert type(k) is ObjStrategy
		self.verified = exverified and all(k.verified for k in self.data) or self.data == []
		for h in range(len(self.data)):
			for g in self.data[:h]:
				if g.name != None:
					assert g.name != self.data[h].name

	def __repr__(self):
		return ",".join([str(i) for i in self.data])
	def wide_repr(self,depth):
		return (",\n"+"\t"*depth).join([str(i) for i in self.data])
	@debugdebug
	def verify(self,scope,errors):
		assert scope.verified
		if self.verified: return self
		zn = []
		for k in range(len(self.data)):
			zn.append(self.data[k].verify(scope+StratSeries(zn,exverified=True),errors))
		return StratSeries(zn,exverified=True)
	@debugdebug
	def substitute(self,revf,repl,errors):
		zn = []
		mmn = revf
		for k in range(len(self.data)):
			zk = self.data[k].substitute(mmn,repl.without(ScopeIntroducer([k.name for k in self.data[:k]])),errors)
			mmn = mostmeagername(mmn,ScopeIntroducer([self.data[k].name]),repl)
			zk.name = mmn[zk.name]
			zn.append(zk)
		return StratSeries(zn,exverified=self.verified)
	def introducer(self):
		return ScopeIntroducer([k.name for k in self.data])
	def refs(self,label):
		if label != None: assert type(label) is str
		for k in self.data:
			if k.refs(label): return True
			if k.name == label: return False
		return False
	def get(self,label):
		if type(label) is int:
			if label>=len(self.data): return None
			return self.data[label]
		for t in reversed(self.data):
			if t.name == label:
				return t
		return None
	def __add__(self,other):
		assert type(other) is StratSeries

		j = []
		mmn = RenamerObject()
		forb = [y.name for y in other.data]

		# errout = "P" in [i.name for i in self.data] and "P$1" in [i.name for i in self.data] and "P" in forb

		# if errout: print("-=-=-=-=-=-=-=-=-")
		# if errout: print([i.name for i in self.data])
		for p in self.data:
			mn = meagersinglename(forb,p.name)
			if p.name == mn: j.append(p)
			else:
				j.append(copy.copy(p.substitute(mmn,SubsObject(),None)))
				j[-1].name = mn
				mmn.data[p.name] = mn
			forb.append(mn)
		# if errout: print([i.name for i in j])
		for p in other.data:
			j.append(copy.copy(p.substitute(mmn,SubsObject(),None)))
			mmn.data[p.name] = p.name
		# print([i.name for i in j])
		return StratSeries(j,exverified=True)

	def __len__(self):
		return len(self.data)
	def __getitem__(self, key):
		return self.data[key]
	def equate(self,cno,other):
		if len(self) != len(other): return False
		return all(self[i].equate(cno,other[i]) for i in range(len(self)))
class DualSubs:
	def __init__(self,variables,subs=None,bon=None,exverified=False):
		assert type(variables) is StratSeries
		if subs != None: assert type(subs) is SubsObject
		self.variables = variables
		self.subs = subs if subs != None else SubsObject()

		self.bon = ScopeSelectionObject([k.name for k in variables.data if k.name != None]) if bon == None else bon
		assert type(self.bon) is ScopeSelectionObject

		for k in self.subs.subs:
			for j in k.bon.bon():
				if not self.variables.introducer().contains(j):
					assert False

		for h in self.variables:
			if h.name != None:
				assert h.name in [p[1] for p in self.bon.data]
		for h in self.bon.data:
			assert h[1] in [p.name for p in self.variables]

		self.verified = exverified and self.subs.verified and self.variables.verified

	def __repr__(self):
		dh = ""
		for k in self.variables.data:
			for i in self.subs.subs:
				if i.name == k.name:
					hu = copy.copy(i)
					hu.name = None
					dh = dh + str(k)+" = "+str(hu)+","
					break
			else:
				dh = dh + str(k)+","
		if len(dh)>0: dh = dh[:-1]
		return dh
	def wide_repr(self,depth):
		dh = "\n"
		for k in self.variables.data:
			for i in self.subs.subs:
				if i.name == k.name:
					hu = copy.copy(i)
					hu.name = None
					dh = dh + "\t"*depth+str(k)+" = "+hu.wide_repr(depth+1)+",\n"
					break
			else:
				dh = dh + "\t"*depth+str(k)+",\n"

		if len(dh)>1: dh = dh[:-2]
		return dh

	@debugdebug
	def verify(self,scope,errors):
		assert scope.verified
		if self.verified: return self
		shash = self.subs.precompact(scope,self.variables.verify(scope,errors),errors)
		shash.bon = self.bon.rename(shash.bon.asrenamer())
		return shash
	@debugdebug
	def compactify(self,scope,subs,errors):
		vokra = SubsObject(subs.substitute(self.bon.asrenamer(),SubsObject(),None).subs + self.subs.subs)
		return DualSubs(self.variables,vokra).verify(scope,errors)

	@debugdebug
	def substitute(self,revf,repl,errors):
		vasr = self.variables.substitute(revf,repl,errors)
		mmn = mostmeagername(revf,self.variables.introducer(),repl)
		zon = self.bon.rename(mmn)
		subs = self.subs.replacebon(mmn).substitute(revf,repl,errors)

		return DualSubs(vasr,subs,zon,exverified=self.verified)
	def refs(self,label):
		label = self.bon[label]
		return self.variables.refs(label) or self.subs.refs(label) and not self.variables.introducer().contains(label)


	def getv(self,name):
		if type(name) is not int and not self.bon.upperintroducer().contains(name): return None
		return self.variables.get(self.bon[name])


	def equate(self,cno,other):
		vno = cno.sertequiv(self.bon.introducer(),other.bon.introducer())
		return self.variables.equate(vno,other.variables) and self.subs.equate(vno,other.subs)
	def availvariables(self):

		for k in range(len(self.variables)):
			if self.variables[k].name in [j.name for j in self.subs.subs]:
				for o in self.variables.data[k+1:]:
					if o.refs(self.variables[k].name):
						assert False

		return StratSeries([k for k in self.variables.data if k.name not in [j.name for j in self.subs.subs]])




#-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=










class ObjKindTemplateHolder(ObjKind):
	def __init__(self,src,subs,pos=None,exverified=False):
		assert issubclass(type(src),ObjKind) and type(subs) is SubsObject
		self.src = src
		self.subs = subs
		transferlines(self,pos)
		self.verified = exverified and self.src.verified and type(self.src) is ObjKindReferenceTree

	def __repr__(self):
		return str(self.src)+"<"+str(self.subs)+">"
	def wide_repr(self,depth):
		return self.src.wide_repr(depth)+"<"+str(self.subs)+">"
	@debugdebug
	def verify(self,scope,carry,errors):
		errors.takeblame(self)
		if self.verified: return self
		yu = self.src.verify(scope,None,errors)
		if type(yu) is ObjKindTemplateHolder:
			return ObjKindTemplateHolder(src=yu.src,subs=SubsObject(yu.subs.subs+self.subs.subs),pos=self,exverified=True)

		if type(yu) is ObjKindTypeUnion:
			return yu.compactify(scope,self.subs,errors)

		if type(yu) is ObjKindReferenceTree:
			return ObjKindTemplateHolder(src=yu,subs=self.subs,pos=self,exverified=True)

		raise errors.error("Substitution is only supported on unions.")
	@debugdebug
	def substitute(self,revf,repl,errors):
		return ObjKindTemplateHolder(self.src.substitute(revf,repl,errors),self.subs.substitute(revf,repl,errors),pos=self,exverified=self.verified)
	def refs(self,label):
		return self.src.refs(label) or self.subs.refs(label)
	def equate(self,cno,other):
		if type(other) is not ObjKindTemplateHolder: return False
		return self.src.equate(cno,other.src) and self.subs.equate(cno,other.subs)


class ObjKindReferenceTree(ObjKind):
	def __init__(self,lvlup=None,args=None,subs=None,src=None,upcast=None,name=None,pos=None,verprot=None):
		if args == None:
			self.args = SubsObject()
			assert lvlup == None
		elif type(args) is SubsObject:
			self.args = args
			assert lvlup == None
		else:
			ijuh = []
			if lvlup == None:
				for z in range(len(args)):
					ijuh.append(IndividualSub(None,ScopeIntroducer([]),args[z],[]))
			else:
				assert len(lvlup) == len(args)
				for z in range(len(args)):
					ijuh.append(IndividualSub(None,ScopeIntroducer(lvlup[z]),args[z],[]))
			self.args = SubsObject(ijuh)

		if subs != None: assert type(subs) is SubsObject
		if src != None: assert issubclass(type(src),ObjKind)
		if name != None: assert type(name) is str or (src != None and type(name) is int)
		self.forgiveLvlup = False
		self.name = name
		self.subs = subs if subs != None else SubsObject()
		self.src = src
		transferlines(self,pos)
		if upcast != None:
			assert args == None
			assert subs == None
			assert src == None
			assert lvlup == None
			assert name == None

			self.column = upcast.column
			self.row = upcast.row
			self.name = upcast.name

			assert len(upcast.lvlup) <= len(upcast.args)
			dfji = []
			for z in range(len(upcast.args)):
				dfji.append(IndividualSub(None,
					ScopeIntroducer([] if z>=len(upcast.lvlup) else upcast.lvlup[z]),
					ObjKindReferenceTree(upcast=upcast.args[z]),[]))
			self.args = SubsObject(dfji)
			self.forgiveLvlup = True
		assert type(self.args) is SubsObject
		assert type(self.subs) is SubsObject



		if   verprot == None:
			self.verified = False
		elif verprot == 0:
			self.verified = self.src.verified
		elif verprot == 1:
			self.verified = self.src.verified and self.args.verified
		elif verprot == 2:
			assert self.src == None
			self.verified = self.args.verified
		else: assert False


		self.verprot = verprot if self.verified else None

		if self.verified: assert self.verprot != None


	def __repr__(self):
		lab = ""
		if self.src != None: lab = str(self.src)+"."
		lab = lab+str(self.name)
		blad = []
		for u in self.args.subs:
			sna = copy.copy(u)
			sna.name = None
			blad.append(sna)

		if len(self.args) != 0: lab = lab+"("+str(SubsObject(blad))+")"
		return lab
	def wide_repr(self,depth):
		lab = ""
		if self.src != None: lab = self.src.wide_repr(depth)+"."
		lab = lab+str(self.name)
		blad = []
		for u in self.args.subs:
			sna = copy.copy(u)
			sna.name = None
			blad.append(sna)

		if len(self.args) != 0:
			lab = lab+"("+SubsObject(blad).oblong_repr(depth+1)+")"
		return lab
	@debugdebug
	def verify(self,scope,carry,errors):
		assert scope.verified
		errors.takeblame(self)

		# print("VERIFYING:",self)

		if self.verified: assert self.verprot != None
		if self.verified: return self
		# if self.verified: return self
		# errors.nonfatal("X")

		if self.src == None and len(self.args) == 0 and self.name == "U":
			if carry.src == None and len(carry.args) == 0 and carry.name == "U":
				mogumogu = ObjKindReferenceTree(name="U",verprot=2)
				assert mogumogu.verified
				return mogumogu

		if self.src != None:
			# print("calling src")
			poc = self.src.verify(scope,None,errors)


			if type(poc) is not ObjKindTypeUnion and type(poc) is not ObjKindUnionSet:

				if type(poc) is ObjKindTemplateHolder:
					root = poc.src
					assert type(root) is ObjKindReferenceTree
				if type(poc) is ObjKindReferenceTree:
					root = poc

				gmo = root.gentype(scope,errors)

				sgig = None

				# print("-=-=-=-=-=-=-=-==-=-->>>>>>>",self.name,gmo)
				if type(gmo) is ObjKindTypeUnion:
					t = gmo.subs.getv(self.name)
					# print("")
					if t != None:
						# print("BAMBAMBAM")
						sgig = self.arginternal(scope,t,carry,errors)
				# else:
				# 	print("-=-failurefailurefailurefailure>>>>",self.name,gmo)

				smomomo = ObjKindReferenceTree(src=poc,args=self.args if sgig==None else sgig,subs=self.subs,name=self.name,pos=self,verprot=int(sgig!=None))
				assert smomomo.verified
				return smomomo

			blcarry = poc.subs.get(self.name)

			if blcarry == None:
				raise errors.error("No such property exists or the property exists but was not defined.")
			if len(blcarry.bon) > 0:
				raise errors.error("The property accessed here is dependantly typed and refers to a variable that is unspecified. (Property cannot be used in static context.)")

			t = blcarry.expected
			if t == None:
				raise errors.error("Unable to infer type for:"+str(self.name))
			duke = self.arginternal(scope,t,carry,errors)#you sure you don't need to remember this????
			mode = blcarry.obj.substitute(RenamerObject(),SubsObject(subsmake(blcarry.si,duke,errors)),errors)
			# print("calling mode")
			return mode.verify(scope,carry,errors.tack())

		t = scope.get(self.name)
		if t == None:
			raise errors.error("Referenced variable not in scope:"+self.name)

		# print("calling arginternal")
		snot = self.arginternal(scope,t,carry,errors)
		# snot = self.args#fix this please
		smomomo = ObjKindReferenceTree(args=snot,name=self.name,pos=self,verprot=2)
		assert smomomo.verified
		return smomomo
	def gentype(self,scope,errors):
		t = scope.get(self.name)
		if t == None:
			raise errors.error("Referenced variable not in scope:"+self.name)
		exptyoe = t.type.substitute(RenamerObject(),self.args,errors)
		exptyoe = exptyoe.verify(scope,ObjKindReferenceTree(name="U",verprot=2),errors.tack())
		return exptyoe
	def arginternal(self,scope,t,carry,errors):
		if len(self.args) != len(t.args): raise errors.error("Wrong argument count.")

		if self.verified: assert self.verprot != None

		fas = []
		for j in range(len(self.args)):
			mogol = self.args.subs[j]
			if len(self.args.subs[j].si) != len(t.args[j].args):
				if self.forgiveLvlup and len(self.args.subs[j].si) < len(t.args[j].args):
					mogol = ScopeIntroducer(self.args.subs[j].si.data+[None for n in range(len(t.args[j].args)-len(self.args.subs[j].si))])
				else:
					raise errors.error("Wrong number of introduced parameters. expected "+str(len(t.args[j].args))+", got "+str(len(self.args.subs[j].si)),self.args.subs[j].obj)
			fas.append(mogol)

		snot = SubsObject(fas).precompact(scope,t.args,errors,onlycomplete=True,argmode=True).subs
		assert type(snot) is SubsObject

		if carry != None:
			exptyoe = t.type.substitute(RenamerObject(),snot,errors)
			if str(exptyoe) == "GT(ara,_)":
				raise errors.error("locked in recursive loop...")
			exptyoe = exptyoe.verify(scope,ObjKindReferenceTree(name="U",verprot=2),errors.tack())

			def recurstep(exptyoe):
				valids = 0
				if exptyoe.equate(CrossNameObject(),carry):
					valids += 1
				elif type(exptyoe) is ObjKindTypeUnion:
					for j in exptyoe.subs.availvariables():
						if len(j.args) == 0:
							valids += recurstep(j.type)
				return valids

			valids = recurstep(exptyoe)

			if valids > 1:
				errors.nonfatal("unable to infer which member to extract from composite type")
			if valids == 0:
				errors.nonfatal(str(exptyoe)+" =/= "+str(carry))
		return snot
	@debugdebug
	def substitute(self,revf,repl,errors):
		if self.verified: assert self.verprot != None

		yobi = self.args.substitute(revf,repl,errors)
		if self.src != None:
			return ObjKindReferenceTree(args=yobi,src=self.src.substitute(revf,repl,errors),name=self.name,pos=self,verprot=self.verprot)
		i = repl.get(self.name)
		if i == None:
			return ObjKindReferenceTree(args=yobi,name=revf[self.name],pos=self,verprot=self.verprot)

		gam = i.obj.substitute(revf.alternate(),SubsObject(subsmake(i.si,yobi,errors)),errors)
		gam.verified = False
		gam.verprot = None
		return gam
	def render(self,scope,carry,errors):
		soijfasijef


	def equate(self,cno,other):
		if type(other) is not ObjKindReferenceTree: return False
		if not cno.equivalen(self.name,other.name): return False
		if self.src == None and other.src == None: return True
		if self.src == None or other.src == None: return False
		return self.args.equate(cno,other.args)
	def refs(self,label):

		if self.verified: assert self.verprot != None

		if self.src == None and self.name == label: return True
		if self.args.refs(label): return True
		if self.src != None and self.src.refs(label): return True
		return False

class ObjKindUnionSet(ObjKind):
	def __init__(self,subs=None,parsed=None,inherited=None,pos=None,verprot=None):
		self.subs = SubsObject() if subs == None else subs
		transferlines(self,pos)
		if parsed != None:
			assert subs == None
			self.subs = parsesubsfromsrc(parsed[0])
		self.inherited = [] if inherited == None else inherited

		if   verprot == None:
			self.verified = False
		elif verprot == 0:
			self.verified = True
		elif verprot == 1:
			self.verified = self.subs.verified
		else: assert False
		self.verprot = verprot if self.verified else None

	def __repr__(self):
		return "("+str(self.subs)+")"
	def wide_repr(self,depth):
		return "("+self.subs.wide_repr(depth+1)+"\n"+"\t"*depth+")"
	@debugdebug
	def verify(self,scope,carry,errors):
		errors.takeblame(self)
		# if self.verified and self.completed: return self
		if carry == None:
			ewgross = copy.copy(self)
			ewgross.verified = True
			ewgross.verprot = 0
			return ewgross

		assert issubclass(type(carry),ObjKind)
		if type(carry) is not ObjKindTypeUnion:
			raise errors.error("Can't pair keyword arguments to static type.")

		vodof = SubsObject(self.subs.without(ScopeIntroducer(self.inherited)).subs+carry.subs.subs.subs)

		gorf = ObjKindUnionSet(subs=vodof.precompact(scope,carry.subs.variables,errors,onlycomplete=True).subs,inherited=[k.name for k in carry.subs.subs.subs],pos=self,verprot=1)

		assert gorf.verified
		return gorf
	@debugdebug
	def substitute(self,revf,repl,errors):
		return ObjKindUnionSet(subs=self.subs.substitute(revf,repl,errors),inherited=self.inherited,pos=self,verprot=self.verprot)
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry,errors):
		union

	def equate(self,cno,other):
		if type(other) is not ObjKindUnionSet: return False
		return self.subs.equate(cno,other.subs)

class ObjKindTypeUnion(ObjKind):
	def __init__(self,parsed=None,subs=None,variables=None,pos=None,exverified=False):
		transferlines(self,pos)
		if parsed != None:
			assert subs == None
			assert variables == None
			variables = [gh.children[0] for gh in parsed]
			argh = []
			for n in range(len(variables)):
				if len(parsed[n].children)==2:
					if variables[n].name != None:
						argh.append(IndividualSub(variables[n].name,ScopeIntroducer([j.name for j in variables[n].args]),parsed[n].children[1],[j.name for j in variables[:n] if j.name != None]))
			self.subs = DualSubs(StratSeries(variables),SubsObject(argh))
		else:
			if type(subs) is DualSubs:
				assert variables == None
				self.subs = subs
			else:
				subi = SubsObject() if subs == None else subs
				vari = StratSeries() if variables == None else variables if type(variables) is StratSeries else StratSeries(variables)
				self.subs = DualSubs(vari,subi)
		self.verified = exverified and self.subs.verified
	def __repr__(self):
		return "{"+str(self.subs)+"}"
	def wide_repr(self,depth):
		return "{"+self.subs.wide_repr(depth+1)+"\n"+"\t"*depth+"}"

	@debugdebug
	def verify(self,scope,carry,errors):
		assert scope.verified
		errors.takeblame(self)
		if self.verified: return self
		return ObjKindTypeUnion(subs=self.subs.verify(scope,errors),pos=self,exverified=True)
	@debugdebug
	def compactify(self,scope,subs,errors):
		return ObjKindTypeUnion(subs=self.subs.compactify(scope,subs,errors),pos=self,exverified=True)
	@debugdebug
	def substitute(self,revf,subs,errors):
		return ObjKindTypeUnion(subs=self.subs.substitute(revf,subs,errors),pos=self,exverified=self.verified)
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry,errors):
		oafdjosidfjoasidf



	def equate(self,cno,other):
		if type(other) is not ObjKindTypeUnion: return False
		return self.subs.equate(cno,other.subs)


class ObjStrategy:
	def __init__(self,args=None,parsed=None,ty=None,name=None,upcast=None,pos=None,exverified=False):
		self.args = StratSeries() if args == None else StratSeries(args) if isinstance(args,list) else args
		self.name = name
		self.type = ty
		transferlines(self,pos)
		if parsed != None:
			assert args==None
			assert ty==None
			assert name==None
			assert upcast==None
			self.type = parsed[-1]
			if len(parsed)>1 and isinstance(parsed[-2],str):
				self.name = parsed[-2]
				self.args = StratSeries([arg for arg in parsed[0:-2]])
			else:
				self.args = StratSeries([arg for arg in parsed[0:-1]])
		if upcast != None:
			assert args==None
			assert ty==None
			assert name==None
			self.column = upcast.column
			self.row = upcast.row
			self.name = upcast.name
			self.type = ObjKindReferenceTree(upcast=upcast.type)
			self.args = StratSeries([ObjStrategy(upcast=i) for i in upcast.args])
		# print(type(self.type))
		assert issubclass(type(self.type),ObjKind)
		assert type(self.args) is StratSeries

		# for h in range(len(self.args)):
		# 	for g in self.args.data[:h]:
		# 		if g.name != None:
		# 			assert g.name != self.args[h].name

		self.verified = exverified and self.type.verified and self.args.verified

	def __repr__(self):
		if len(self.args) != 0:
			if self.name != None: return "["+",".join([str(k) for k in self.args])+"]"+self.name+":"+str(self.type)
			else: return "["+",".join([str(k) for k in self.args])+"]"+str(self.type)
		else:
			if self.name != None: return self.name+":"+str(self.type)
			else: return str(self.type)


	def refsany(self,si):
		def minjcontains(j):
			if isinstance(j,list):
				return any(minjcontains(o) for o in j)
			return self.refs(j)
		return minjcontains(si.dat)

	@debugdebug
	def verify(self,scope,errors):
		assert scope.verified
		errors.takeblame(self)
		if self.verified: return self
		verargs = self.args.verify(scope,errors)
		return ObjStrategy(
			args=verargs,
			ty=self.type.verify(scope+verargs,ObjKindReferenceTree(name="U",verprot=2),errors),
			name=self.name,
			pos=self,
			exverified=True
		)
	@debugdebug
	def substitute(self,revf,repl,errors):
		mmn = mostmeagername(revf,self.introducer(),repl)
		return ObjStrategy(args=self.args.substitute(revf,repl,errors),ty=self.type.substitute(mmn,repl.without(self.args.introducer()),errors),name=self.name,pos=self,exverified=self.verified)

	def refs(self,label):
		if self.args.refs(label): return True
		return not self.args.introducer().contains(label) and self.type.refs(label)
	def introducer(self):
		return ScopeIntroducer([k.name for k in self.args])

	@debugdebug
	def reformat(self,scope,mog,errors):
		errors.takeblame(self)
		assert scope.verified
		if len(mog) != len(self.args):
			raise errors.error("Mechanical error (subside): Highly illegal compactify call.")
		if len(mog) == 0: return self

		assert not self.refsany(mog)


		def minjcontains(j):
			if isinstance(j,list):
				mo =[minjcontains(s) for s in j]
				if mo == []: return 0
				return min(mo)
			if len(j)==3 and j[1] == ":":
				try: return int(j[0])
				except: return 0
			return 0


		def arbirow(depth,length):
			return ScopeIntroducer([str(depth)+":"+str(h) for h in range(length)])

		def simconvert(k,depth):
			po=[]
			for i in range(len(k.args)):
				ja = arbirow(depth+1,len(k.args[i].args))

				# k.args[i]

				po.append(IndividualSub(None,ja,ObjKindReferenceTree(name=str(depth)+":"+str(i),args=simconvert(k.args[i],depth+1)),[]))
			return SubsObject(po)

		def croconvert(j,k,sfar):
			if isinstance(j,list):
				assert len(k.args) == 0
				assert type(k.type) is ObjKindTypeUnion
				availb = k.type.subs.availvariables()
				assert len(availb) == len(j)

				shar = []
				for i in range(len(j)):
					nsfar  = minjcontains(j[i])

					# availb[i]
					# scope: previous subs...

					shar.append(IndividualSub(None,arbirow(nsfar,len(availb[i].args)),croconvert(j[i],availb[i],nsfar),[]))

				return ObjKindUnionSet(subs=SubsObject(shar))
			return ObjKindReferenceTree(name=j,args=simconvert(k,sfar))

		def populate(j,k,repl,prevs):
			if isinstance(j,list):
				if len(k.args) != 0:
					raise errors.error("Mechanical error (subside): Function-to-tuple unwrapping is not supported.")
				if type(k.type) is not ObjKindTypeUnion:
					raise errors.error("Mechanical error (subside): non-unionset unwrapped in given paramter for eval. "+str(mog)+" , "+str(self))

				availb = k.type.subs.availvariables()

				if len(availb) != len(j):
					raise errors.error("Mechanical error (subside): Illegal unwrap length.")


				res = StratSeries()
				for i in range(len(j)):
					res = res + populate(j[i],availb[i],repl,prevs+res)
				return res

			try:
				mold = copy.copy(k.substitute(RenamerObject(),repl,errors))
				mold = mold.verify(prevs,errors)
			except ErrorObject: assert False
			mold.name = j
			return StratSeries([mold],exverified=True)

		nargs = StratSeries()
		assert nargs.verified
		uio = []
		for g in range(len(mog)):
			try:
				ays = SubsObject(uio).precompact(scope+self.args+nargs,StratSeries(self.args.data[:g],exverified=True),errors,onlycomplete=True)
			except ErrorObject: assert False

			# concatenating strategies before casting from array causes duplicate protections to fail......

			assert type(scope) is StratSeries
			assert type(nargs) is StratSeries
			assert type(nargs.data) is list
			nargs = nargs + populate(mog.dat[g],self.args[g],ays.subs,scope+nargs)

			for k in nargs.data:
				assert k.verified
			assert nargs.verified
			nsfar = minjcontains(mog.dat[g])
			moh = croconvert(mog.dat[g],self.args[g],nsfar)
			uio.append(IndividualSub(self.args[g].name,arbirow(nsfar,len(self.args[g].args)),moh,[]))
		try:
			shaja = SubsObject(uio).precompact(scope+self.args+nargs,self.args,errors,onlycomplete=True)
		except ErrorObject: assert False
		# 	print("wassup doc",nargs)
		# 	raise u


		# assert shaja != None
		shaja = shaja.subs
		sja = self.type.substitute(RenamerObject(),shaja,errors)
		return ObjStrategy(name=self.name,ty=sja,args=nargs).verify(scope,errors)


	def equate(self,cno,other):
		if self.name != other.name: return False
		if not self.args.equate(cno,other.args): return False
		if not self.type.equate(cno,other.type): return False
		return True






#erase linononononon



#already verified flags for speed



# separate initfromparse() functions


#make mostmeagername usage more graceful-> split into two, one for individual renamings, one for introducers.


#reduce copies by checking if you'd really be changing things-> this especially concerns reformat
#    might be nice to have a rename function on strategies...






#turn the whole program into one objstrategy


#research reducing copies by doing a substitution lookeahead (does not obsolete verified, because of name replacements)



#forbidden(values) + repl constitute set of unusable variable names... doubleecheck that this is preserved on alternate. After all, the normal set of replacements is hidden and don't get applied to repl............. big hmm.
#      maybe you need to double check all refs with alt... like use alt as a renamer before going to refs(label)



#need to introduce a second equality relation that allows type casts. (Asymmetric, though, so it's not really equaity.)





#make sure that, if an SI gets passed over, that SI.rename should leave the SI unaffected.





#review comments,prints,and assertions, and try/catches, and raises, and returns





