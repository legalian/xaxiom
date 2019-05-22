
from .structures import *
import time
from inspect import getframeinfo, stack, getfullargspec


class ObjKind:
	def refsany(self,si):
		def minjcontains(j):
			if isinstance(j,list):
				return any(minjcontains(o) for o in j)
			return self.refs(j)
		return minjcontains(si.dat)
	def caststo(self,cno,other):
		return self.equate(cno,other)

def upcast_statement(inop):
	dfji = []
	for z in range(len(inop.args)):
		dfji.append(IndividualSub(None,
			ScopeIntroducer([] if z>=len(inop.lvlup) else inop.lvlup[z]),
			upcast_statement(inop.args[z]),[]))
	mod = ObjKindReferenceTree(name=inop.name,pos=inop,args=dfji)
	mod.forgiveLvlup = True
def upcast_strategy(inop):
	pass
	return ObjStrategy(pos=inop,name=inop.name,ty=upcast_statement(inop.type),args=StratSeries([upcast_strategy(i) for i in inop.args]))
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
			# fonodepth -= 1


			zaru = getfullargspec(F)

			for i in range(len(zaru[0])):
				if zaru[0][i] == "scope":
					# print("entering: ",type(args[0]).__name__+"."+janh)
					# print(type(args[i]))
					assert type(args[i]) is StratSeries
					assert args[i].verified


			if janh == "substitute":
				# if args[0].verified and len(args[2]) == 0 and not ahjs.verified:
				# 	print("error on: ",type(args[0]).__name__+"."+janh)
				# 	assert False
				for u in args[2].subs:
					if u.name not in args[1].s and u.name != None:
						print("-="*10)
						print("<><><><->:",args[1].s)
						print("<><><><->:",args[2])
						print("CONCERN:",u.name)
						assert u.name in args[1].s



			ahjs = F(*args,**kwargs)

			if janh == "verify":
				if not ahjs.verified:
					print("error on: ",type(args[0]).__name__+"."+janh)
					assert ahjs.verified


			if janh == "substitute":
				# if args[0].verified and len(args[2]) == 0 and not ahjs.verified:
				# 	print("error on: ",type(args[0]).__name__+"."+janh)
				# 	assert False

				if args[0].verified and all(i.obj.verified and (type(i.obj) is not ObjKindUnionSet or i.obj.verprot == 1) for i in args[2].subs) and not ahjs.verified:
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






class RenamerObject:
	def __init__(self,scope,data=None,alt=None):
		if type(scope) is StratSeries:
			self.s = [k.name for k in scope.flat]
		else:
			self.s = scope
		for x in range(len(self.s)):#safemode
			for y in range(x):#safemode
				assert self.s[x]!=self.s[y]#safemode


		self.data = data if data != None else {}
		self.alt = alt if alt != None else {}

	def alternate(self):
		return RenamerObject(self.s,self.alt,self.data)

	def integrate(self,si):
		def meager(forbidden,intr):
			if intr == None: intr = "%"
			if type(forbidden) is dict: forbidden = forbidden.values()
			if intr not in forbidden: return intr
			g = intr.split("$")
			assert len(g) == 1 or len(g) == 2#safemode
			n = int(g[1]) if len(g) == 2 else 1
			h = g[0]
			while h+"$"+str(n) in forbidden: n+=1
			return h+"$"+str(n)


		repls = copy.copy(self.data)
		pres = []

		if type(si) is ScopeSelectionObject:
			klo = []
			for p in si.data:

				z = meager(self.s+pres,p[1])
				pres.append(z)
				if p[1] != z: repls[p[1]] = z
				klo.append((p[0],z))
			return (ScopeSelectionObject(klo),RenamerObject(self.s+pres,repls,self.alt))


		def croc(intr):
			if isinstance(intr,list):
				return [croc(i) for i in intr]
			z = meager(self.s+pres,intr)
			pres.append(z)
			if intr != z: repls[intr] = z
			return z
		return (ScopeIntroducer(croc(si.dat)),RenamerObject(self.s+pres,repls,self.alt))



	def temper(self,stemp,bon):
		nel = dict([y for y in self.data.items() if y[0] not in stemp])
		for k,v in bon.data:
			yu = self.data.get(k,k)
			if yu != v: nel[v] = yu
		return RenamerObject(self.s,nel,self.alt)

		#the thing you're replacing ought to be in sem




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
	def sertbonequal(self,a,b):
		zon = copy.copy(self.data)
		for x in a.data:
			for y in b.data:
				if x[0]==y[0]:
					zon.append((x[1],y[1]))
		return CrossNameObject(zon)
		#it's entirely possible that the keys won't match up here... that's just something to keep in mind...
		#review this.


class ErrorObject(BaseException):
	blame = None
	rer = []

	def takeblame(obk):
		ErrorObject.blame = obk
	def fatal(err,obk=None):
		ErrorObject.nonfatal(err,obk)
		raise ErrorObject()
	def nonfatal(err,obk=None):
		assert type(err) is str#safemode
		if obk == None:
			assert ErrorObject.blame != None#safemode
			ErrorObject.rer.append((err,ErrorObject.blame))
		else:
			ErrorObject.rer.append((err,obk))

	def reports(window):
		errors = list(dict.fromkeys([(o[0],o[1].row,o[1].column) for o in ErrorObject.rer]))
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
		if len(ErrorObject.rer) == 1:
			return str((ErrorObject.rer[0][0],ErrorObject.rer[0][1].row,ErrorObject.rer[0][1].column))
		return "multiple errors"



class ScopeIntroducer:
	def __init__(self,dat):
		self.dat = dat
		def shmo(o):#safemode
			if isinstance(o,list):#safemode
				for i in o: shmo(i)#safemode
			else:#safemode
				assert type(o) is str or o == None#safemode
		shmo(dat)#safemode
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
		assert type(label) is str#safemode
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
	def __init__(self,name,si,obj,bon,expected=None,exverified=False,inherited=False,slamsubs=None):
		assert type(name) is str or name == None#safemode
		assert type(expected) is ObjStrategy or expected == None#safemode
		assert type(si) is ScopeIntroducer#safemode
		assert issubclass(type(obj),ObjKind)#safemode


		self.name = name
		self.si = si
		self.obj = obj
		self.bon = bon if type(bon) is ScopeSelectionObject else ScopeSelectionObject(bon)
		self.expected = expected
		self.inherited = inherited
		self.slamsubs = slamsubs

		self.verified = exverified and (self.expected == None or self.expected.verified) and self.obj.verified
		if self.expected != None:#safemode
			assert len(si.dat) == expected.args.lenavail()#safemode
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
	def substitute(self,revf,repl):
		nbon,mmn = revf.integrate(self.bon)
		nsi,mmn2 = mmn.integrate(self.si)

		if self.slamsubs == None:
			udh = None
		else:
			nam,mmn2 = mmn2.integrate(ScopeIntroducer([h.name for h in spoken[z][k][0].slamsubs.subs]))
			tscop = []
			for u in range(len(nam.dat)):
				sul = copy.copy(self.slamsubs.subs[u])
				sul.name = nam.dat[u]
				tscop.append(sul)
			udh = SubsObject(tscop)

		uhf = self.obj.substitute(mmn2,repl)

		# jae = None if self.expected == None else self.expected.substitute(revf,repl) this substitute doesn't work wor

		return IndividualSub(self.name,nsi,uhf,nbon,None,exverified=self.verified,inherited=self.inherited,slamsubs=udh)




	def refs(self,label):
		if self.si.contains(label): return False
		return self.obj.refs(label)
	def equate(self,cno,other):
		con = cno.sertequiv(self.si,other.si)
		if con == None: return False
		con = con.sertbonequal(self.bon,other.bon)
		soul = self.obj.equate(con,other.obj)

		if not soul:
			print("WAHHHH",con.data,self.obj,other.obj)
		return soul
	def caststo(self,cno,other):
		con = cno.sertequiv(self.si,other.si)
		if con == None: return False
		con = con.sertbonequal(self.bon,other.bon)
		soul = self.obj.caststo(con,other.obj)

		if not soul:
			print("BOOHOO",con.data,self.obj,other.obj)
		return soul


	@debugdebug
	def unwrapsubs(self,mog,bobo=None,slamsubs=None,prep=None,onlyavailable=False):
		if prep == None: prep = []
		def techdrop(mam):
			hu = mam.obj
			if mam.name == None and mam.expected != None:
				hu = ObjKindUnionSet(subs = [techdrop(i) for i in hu.subs.subs],verprot=1)
			return IndividualSub(None,mam.si,hu,mam.bon,mam.expected,exverified=mam.verified)
		def internalsubsmake(mog,trail,prep):
			if isinstance(mog,list):
				return [i for f in range(len(mog)) for i in internalsubsmake(mog[f],trail+[(f,len(mog))],prep)]
			jog = self.obj
			for s in trail:
				jog = ObjKindReferenceTree(src=jog,name=s,verprot=0)
			return [IndividualSub(mog,ScopeIntroducer(prep+self.si.dat),jog,[] if bobo == None else bobo,exverified=True,slamsubs=slamsubs)]
		if isinstance(mog,list):
			if type(self.obj) is not ObjKindUnionSet:
				return internalsubsmake(mog,[],prep+self.si.dat)
			else:
				return self.obj.subs.unwrapsubs(mog,bobo=bobo,slamsubs=slamsubs,prep=prep+self.si.dat,onlyavailable=onlyavailable)
		else:
			hu = self.obj
			if self.name == None and self.expected != None:
				print("=-=-=-=-=",self)
				hu = ObjKindUnionSet(subs = [techdrop(i) for i in hu.subs.subs],verprot=1)
			return [IndividualSub(mog,ScopeIntroducer(prep+self.si.dat),hu,[] if bobo == None else bobo,exverified=True,slamsubs=slamsubs)]



class SubsObject:
	def __init__(self,data=None,exverified=False):
		if data != None:#safemode
			for k in data: assert type(k) is IndividualSub#safemode
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
	def substitute(self,revf,repl):
		return SubsObject([i.substitute(revf,repl) for i in self.subs],exverified=self.verified)



	@debugdebug
	def unwrapsubs(self,mog,bobo=None,prep=None,slamsubs=None,onlyavailable=False):
		if type(mog) is ScopeIntroducer: mog = mog.dat
		assert type(mog) is not str#safemode


		print("----_>",mog,len([p for p in self.subs if not p.inherited]),len([p for p in self.subs if p.inherited]),onlyavailable)


		if len(mog) < len(self.subs):
			ErrorObject.fatal("Incorrect unwrap length...")
		rtse = []
		t = 0
		for f in self.subs:
			if not (onlyavailable and f.inherited):
				rtse = rtse + f.unwrapsubs(mog[t],bobo=bobo,slamsubs=slamsubs,prep=prep,onlyavailable=onlyavailable)
				t += 1
		if t<len(mog):
			ErrorObject.fatal("Incorrect unwrap length...")

		return rtse



	def __add__(self,other):
		return SubsObject(self.subs+other.subs)



	def without(self,so):
		return SubsObject([d for d in self.subs if not so.contains(d.name)],exverified=self.verified)
	def only(self,so):
		return SubsObject([d for d in self.subs if so.contains(d.name)],exverified=self.verified)
	def refs(self,label):
		# for i in self.subs:
		# 	if i.obj.refs(label) and not i.si.refs(label): return True
		# return False
		return any(i.refs(label) for i in self.subs)


	def get(self,label,errors):
		if type(label) is tuple:
			if label[1]!=len(self.subs): ErrorObject.fatal("mechanical: Wrong number of introduced parameters.")
			return self.subs[label]
		for t in reversed(self.subs):
			if t.name == label:
				return t
		return None



	def render(self,scope):
		for zal in self.subs:#safemode
			assert len(zal.bon) == 0#safemode
		rendercode
		# return [(zal.si.allvars(),zal.obj.verify(scope+zal.expected.args,zal.expected.type)) for zal in self.subs]
	@debugdebug
	def precompact(self,scope,cars,needscomplete=False):
		assert type(cars) is StratSeries#safemode
		assert type(cars.original.dat) is not str#safemode
		spoken = [[[None,k] for k in ScopeIntroducer(o).allvars()] for o in cars.original.dat]
		for j in self.subs:
			if j.name == None:
				for gr in range(len(spoken)):
					zorl = len([o for o in spoken[gr] if o[0]==None])
					if zorl == 0: continue
					joke = [j] if zorl == 1 else j.unwrapsubs(cars.original.dat[gr])
					assert len(joke) == zorl
					t=0
					for z in range(len(spoken[gr])):
						if spoken[gr][z][0] == None:
							spoken[gr][z][0] = joke[t]
							t+=1
					break
				else:
					ErrorObject.fatal("Too many arguments.")
			else:
				found = False
				for gr in range(len(spoken)):
					for yi in range(len(spoken[gr])):
						if spoken[gr][yi][0] == None and spoken[gr][yi][1] == j.name:
							spoken[gr][yi][0] = j
							found = True
							break
					if found: break
				if not found:
					ErrorObject.fatal("Unknown argument specified or already specified: "+j.name)

		sofar = []
		for io in spoken:
			for em in io:
				if em[0] == None:
					if needscomplete:
						if em[1]==None: ErrorObject.fatal("Missing positional argument.")
						ErrorObject.fatal("Missing named argument: "+str(em[1]))
					continue
				for check in em[0].bon.bon():
					if check not in sofar and em[0].obj.refs(check) and not em[0].si.contains(check):
						ErrorObject.fatal("The usage of the following variable violates the well-ordering property: "+check)
				sofar.append(em[0].name)


		for z in range(len(spoken)):
			for k in range(len(spoken[z])):
				if spoken[z][k][0] != None and spoken[z][k][0].slamsubs != None:

					nam,ren = RenamerObject(scope).integrate(ScopeIntroducer([h.name for h in spoken[z][k][0].slamsubs.subs]))

					tscop = []
					for u in range(len(nam.dat)):
						sul = copy.copy(spoken[z][k][0].slamsubs.subs[u])
						sul.name = nam.dat[u]
						tscop.append(sul)

					spoken[z][k][0] = copy.copy(spoken[z][k][0])
					spoken[z][k][0].slamsubs = None
					spoken[z][k][0].obj = spoken[z][k][0].obj.substitute(ren,SubsObject(tscop))


		simpsubs = []
		flatsubs = []
		zndata = []
		znflat = []

		mmn = RenamerObject(scope)

		for z in range(len(spoken)):
			for x in znflat:#safemode
				assert type(x.name) is str#safemode
			pscope = scope+StratSeries(zndata,znflat,original=ScopeIntroducer(cars.original.dat[:z]))
			nname,mmn2 = mmn.integrate(ScopeIntroducer(cars.data[z].name))
			nname = nname.dat

			zaku = cars.data[z].substitute(mmn,SubsObject(flatsubs)).surfacerename(nname)
			assert zaku.verified#safemode

			if type(cars.original.dat[z]) is str or cars.original.dat[z] == None:
				assert len(spoken[z]) == 1#safemode
				if spoken[z][0][0] != None:
					nsi,lmmn = mmn.temper(pscope.original.allvars(),spoken[z][0][0].bon).integrate(spoken[z][0][0].si)
					strud = zaku.reformat(pscope,nsi)
					nobj = spoken[z][0][0].obj.substitute(lmmn,SubsObject(flatsubs)).verify(pscope+strud.args.variables,strud.type)
					
					orjambo = []
					jambo = []

					for jam in range(len(znflat)):
						if zaku.refs(znflat[jam].name) or nobj.refs(znflat[jam].name):
							jambo.append(znflat[jam].name)
							orjambo.append((cars.original.dat[jam],znflat[jam].name))

					simpsubs.append(IndividualSub(cars.data[z].name,nsi,nobj,orjambo,zaku,exverified=True,inherited=spoken[z][0][0].inherited))
					flatsubs.append(IndividualSub(nname,nsi,nobj,jambo,zaku,exverified=True))
				zndata.append(zaku)
				znflat.append(zaku)

				for x in znflat:#safemode
					assert type(x.name) is str#safemode
				mmn = mmn2
			else:
				# snscope = pscope+zaku.args.variables

				akar = []
				vlode = []

				zador = zaku.args.bgroup([k.name for k in pscope.flat],zaku.args.variables.introducer())
				# print("---->",cars.data[z])
				# print("---->",zaku)
				# print(cars.original.dat[z])
				zomm = zaku.ultimrename([k.name for k in pscope.flat],DualSubs(StratSeries(),exverified=True),[k.name for k in zaku.type.subs.availvariables()],flat=True,onlyavailable=True)


				for k in range(len(spoken[z])):
					nlorname,mmn2 = mmn.integrate(ScopeIntroducer(zomm[k].name))
					nlorname = nlorname.dat
					hzaku = zomm[k].substitute(mmn,SubsObject(flatsubs)).surfacerename(nlorname)

					if spoken[z][k][0] != None:
						nsi,lmmn = mmn.temper(pscope.original.allvars(),spoken[z][k][0].bon).integrate(spoken[z][k][0].si)
						ansi = ScopeIntroducer(nsi.dat[len(zaku.args.variables.data):])
						pnsi = ScopeIntroducer(nsi.dat[:len(zaku.args.variables.data)])
						if len(spoken[z][k][0].si.dat)<len(zaku.args.variables.data):
							ErrorObject.fatal("Not enough introduced parameters for this pattern.")
						nobj = spoken[z][k][0].obj.substitute(lmmn,SubsObject(flatsubs+zador.unwrapsubs(pnsi)))


						# orjambo = []
						jambo = []
						for jam in vlode:
							if hzaku.refs(jam) or nobj.refs(jam):
								jambo.append(jam)
								# orjambo.append(<><><>)

						akar.append(IndividualSub(nlorname,ansi,nobj,jambo,inherited=True))#<--- nlorname,jambo needs to be changed here.
						flatsubs.append(IndividualSub(nlorname,nsi,nobj,jambo,hzaku,exverified=True))
						for x in znflat:#safemode
							assert type(x.name) is str#safemode
					znflat.append(hzaku)
					vlode.append(nlorname)

					mmn = mmn2



				zot = SubsObject(zaku.type.subs.subs.subs+akar).precompact(scope,zaku.type.subs.variables,override=ScopeIntroducer(cars.original.dat[z]))



				zndata.append(ObjStrategy(args=zaku.args,ty=ObjKindTypeUnion(subs=zot),name=zaku.name))

		zalog = DualSubs(StratSeries(zndata,znflat,original=cars.original),SubsObject(simpsubs,exverified=True),exverified=True)
		assert zalog.verified#safemode
		return zalog




	def postcompact(self,scope,subs):
		return subs.compactify(scope,SubsObject([k for k in self.subs if not k.inherited]),needscomplete=True).supersubs()



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
			if not self.subs[a].equate(cno,other.subs[b]):
				return False
			b+=1
		return True
	def caststo(self,cno,other):
		#every sub in self also in other
		if len(self) > len(other): return False
		ja = [False]*len(self)
		jb = [False]*len(self)
		for a in range(len(self)):
			if self.subs[a].name == None: continue
			for b in range(len(self)):
				if self.subs[a].name == other.subs[b].name:
					if not self.subs[a].caststo(cno,other.subs[b]): return False
					ja[a] = True
					jb[b] = True
					break

		b=0
		for a in range(len(self)):
			if ja[a]: continue
			while jb[b]: b+=1
			if not self.subs[a].caststo(cno,other.subs[b]):
				return False
			b+=1
		return True
class StratSeries:
	def __init__(self,data=None,flatdata=None,original=None):
		self.data = [] if data == None else data
		if self.data == []: flatdata = []
		for k in self.data: assert type(k) is ObjStrategy#safemode
		self.verified = all(k.verified for k in self.data) and flatdata != None

		self.flat = flatdata
		if self.flat != None:#safemode
			for k in self.flat:#safemode
				assert type(k) is ObjStrategy#safemode
				assert type(k.name) is str#safemode



		assert (self.flat == None) != (self.verified) #safemode
		for h in range(len(self.data)):#safemode
			for g in self.data[:h]:#safemode
				if g.name != None:#safemode
					assert g.name != self.data[h].name#safemode
		if self.flat != None:#safemode
			for j in self.flat: assert j.verified#safemode
			for h in range(len(self.flat)):#safemode
				for g in self.flat[:h]:#safemode
					if g.name != None:#safemode
						assert g.name != self.flat[h].name#safemode


		self.original = self.introducer() if original == None else original

	def __repr__(self):
		return ",".join([str(i) for i in self.data])
	def wide_repr(self,depth):
		return (",\n"+"\t"*depth).join([str(i) for i in self.data])
	@debugdebug
	def verify(self,scope):
		if self.verified: return self
		zvn = []
		zn = []
		mmn = RenamerObject(scope)
		for k in range(len(self.data)):
			nm,nmmn = mmn.integrate(ScopeIntroducer(self.data[k].name))
			pscope = StratSeries(zn,zvn,original=ScopeIntroducer(self.original.dat[:k]))
			p = self.data[k].surfacerename(nm.dat).substitute(mmn,SubsObject()).verify(scope+pscope)
			mmn=nmmn
			zn.append(p)
			zvn = zvn + p.split([k.name for k in scope.flat]+[k.name for k in zvn])
		return StratSeries(zn,zvn,original=self.original)
	@debugdebug
	def substitute(self,revf,repl):
		zn = []
		zvn = []
		mmn = revf

		for k in range(len(self.data)):
			zk = self.data[k].substitute(mmn,repl)
			nname,mmn = mmn.integrate(ScopeIntroducer(self.data[k].name))
			zn.append(zk.surfacerename(nname.dat))

		if self.flat == None: return StratSeries(zn,original=self.original)

		mmn = revf

		for k in range(len(self.flat)):
			zk = self.flat[k].substitute(mmn,repl)
			nname,mmn = mmn.integrate(ScopeIntroducer(self.flat[k].name))
			zvn.append(zk.surfacerename(nname.dat))

		return StratSeries(zn,zvn,original=self.original)

	def introducer(self):
		return ScopeIntroducer([k.name for k in self.data])
	def refs(self,label):
		if label != None: assert type(label) is str#safemode
		for k in self.data:
			if k.refs(label): return True
			if k.name == label: return False
		return False
	def get(self,label):
		if type(label) is tuple:
			if label[1]!=len(self.data): ErrorObject.fatal("mechanical: Wrong number of introduced parameters.")
			return self.data[label]
		for t in reversed(range(len(self.flat))):
			# if self.original.allvars()[t] == label:
			if self.flat[t].name == label:
				return self.flat[t]
		return None
	def __add__(self,other):
		return StratSeries(self.data+other.data,self.flat+other.flat,original=ScopeIntroducer(self.original.dat+other.original.dat))


	def equate(self,cno,other):
		if len(self) != len(other): return False
		for r in range(len(self)):
			if not self[i].equate(cno,other[i]): return False
			cno = cno.sertequiv(ScopeIntroducer(self[i].name),ScopeIntroducer(other[i].name))
		return True



class DualSubs:
	def __init__(self,variables,subs=None,exverified=False):
		assert type(variables) is StratSeries#safemode
		if subs != None: assert type(subs) is SubsObject#safemode
		self.variables = variables
		self.subs = subs if subs != None else SubsObject()


		for k in self.subs.subs:#safemode
			for j in k.bon.bon():#safemode
				if not self.variables.original.contains(j):#safemode
					assert False#safemode



		self.verified = exverified and self.subs.verified and self.variables.verified

	def __repr__(self):
		dh = ""
		for k in self.variables.data:
			for i in range(len(self.subs.subs)):
				if self.variables.original.dat[i] == k.name:
					hu = copy.copy(self.subs.subs[i])
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
			for i in range(len(self.subs.subs)):
				if self.variables.original.dat[i] == k.name:
					hu = copy.copy(self.subs.subs[i])
					hu.name = None
					dh = dh + "\t"*depth+str(k)+" = "+hu.wide_repr(depth+1)+",\n"
					break
			else:
				dh = dh + "\t"*depth+str(k)+",\n"

		if len(dh)>1: dh = dh[:-2]
		return dh
	@debugdebug
	def verify(self,scope,needscomplete=False):
		if self.verified: return self

		varver = self.variables.verify(scope)


		she = []
		for he in self.subs.subs:
			she = she + he.unwrapsubs(he.name,bobo=he.bon,slamsubs=he.slamsubs)

		shash = SubsObject(she).precompact(scope,varver,needscomplete=needscomplete)

		# if self.sphsubs != None:
		# 	she = []
		# 	for o in self.sphsubs:
		# 		he = IndividualSub(None,o[1],o[2],[])
		# 		she = she + he.unwrapsubs(o[0],bobo=o[3])
		# 	shash = SubsObject(she).precompact(scope,varver,needscomplete=needscomplete)
		# else:
		# 	shash = self.subs.precompact(scope,varver,needscomplete=needscomplete)
		# shash.bon = self.bon.rename(shash.bon.asrenamer())
		return shash
	@debugdebug
	def compactify(self,scope,subs,needscomplete=False):
		assert self.verified#safemode
		yam = []
		for s in self.subs.subs:
			r = copy.copy(s)
			r.inherited = True
			yam.append(r)
		return DualSubs(self.variables,SubsObject(yam+subs.subs)).verify(scope,needscomplete=needscomplete)
	@debugdebug
	def substitute(self,revf,repl):
		vasr = self.variables.substitute(revf,repl)
		null,mmn = revf.integrate(self.variables.introducer())
		subs = self.subs.substitute(mmn,repl)
		return DualSubs(vasr,subs,exverified=self.verified)
	def refs(self,label):

		# individualsub does redirect over bon...
		# dont forget to carry original through all stratseries operations.

		return self.variables.refs(label) or self.subs.refs(label) and not self.variables.introducer().contains(label)

	def __add__(self,other):
		return DualSubs(self.variables+other.variables,self.subs+other.subs,exverified=self.verified and other.verified)



	def supersubs(self):
		assert self.verified#safemode

		yak = copy.copy(self.subs.subs)
		for p in range(len(self.variables.data)):
			if type(self.variables.data[p].name) is list:
				assert type(self.variables.data[p].type) is ObjKindTypeUnion#safemode

				yak.append(IndividualSub(None,self.variables.data[p].args.semavail(),ObjKindUnionSet(subs=self.variables.data[p].type.subs.supersubs(),exverified=True),[],self.variables.data[p],exverified=True))

		return SubsObject(yak,exverified=True)


		# untrance = {}
		# assert len(self.variables.original.dat) == len(self.variables.data)
		# for e in range(len(self.variables.original.dat)):
		# 	untrance[self.variables.original.dat[e]] = self.variables.data[e].name

		# yak = []
		# for j in self.subs.subs:
		# 	kp = copy.copy(j)
		# 	kp.name = untrance[kp.name]
			# assert len(kp.bon) == 0
		# 	yak.append(kp)
		# for p in self.variables.data:
		# 	flatvars = ScopeIntroducer(p.name).allvars()
		# 	if type(p.name) is not str and type(p.type) is ObjKindTypeUnion:
		# 		zel = p.type.subs.supersubs()
		# 		for o in range(len(zel)):
		# 			kp = copy.copy(zel[o])
		# 			kp.name = flatvars[o]
		# 			kp.si = ScopeIntroducer([k.name for k in p.args.availvariables()]+kp.si.dat)
		# 			yak.append(kp)

		# return SubsObject(yak,inherited=inherited,exverified=True)





	def getv(self,name):
		return self.variables.get(name)


	def equate(self,cno,other):
		vno = cno.sertequiv(self.variables.original,other.variables.original)
		return self.variables.equate(cno,other.variables) and self.subs.equate(vno,other.subs)
	def caststo(self,cno,other):
		vno = cno.sertequiv(self.variables.original,other.variables.original)
		return self.variables.equate(cno,other.variables) and self.subs.caststo(vno,other.subs)

	def availvariables(self):
		assert self.verified#safemode

		for k in range(len(self.variables.data)):#safemode
			if self.variables.data[k].name in [j.name for j in self.subs.subs]:#safemode
				for o in self.variables.data[k+1:]:#safemode
					if o.refs(self.variables[k].name):#safemode
						assert False#safemode
		res = []
		for t in range(len(self.variables.data)):
			for j in self.subs.subs:
				if j.name == self.variables.original.dat[t]: break
			else:
				res.append(self.variables.data[t])
		return res
	def lenavail(self):
		l=0
		for t in range(len(self.variables.data)):
			for j in self.subs.subs:
				if j.name == self.variables.original.dat[t]: break
			else:
				l = l + 1
		return l
	def semavail(self):
		return ScopeIntroducer([k.name for k in self.variables.data if k.name not in [l.name for l in self.subs.subs]])

	@debugdebug
	def ultimrename(self,semscope,prescope,mog,onlyavailable=False):
		assert self.verified#safemode
		if type(mog) is ScopeIntroducer: mog = mog.dat
		assert mog != None#safemode

		maxln = self.lenavail() if onlyavailable else len(self.variables.data)
		assert type(mog) is not str#safemode
		if len(mog) != maxln:
			ErrorObject.fatal("Mechanical error (subside): Wrong number of arguments for unwrap.")
		voexsubs = SubsObject()
		jan  = []
		comscope = []
		erscope = semscope
		t=0
		for i in range(len(self.variables.data)):
			# ntrail = trail+[(t,maxln)] if type(mog) is str else trail
			# nmog = mog if type(mog) is str else mog[t]
			for j in self.subs.subs:
				if j.name == self.variables.original.dat[i]:
					assert type(self.variables.data[i].name) is str#safemode
					# yu = copy.copy(j).substitute(erscope,voexsubs)
					# yu.name = self.variables[i].name
					# voexsubs.subs.append(yu)<-    thing is... if you're verified, you won't need to substitute anything like this, so...

					nu = copy.copy(j).substitute(erscope,voexsubs)
					nu.name = None
					nu.inherited = True
					jan.append(nu)
					if not onlyavailable:
						shim = self.variables.data[i].substitute(RenamerObject(erscope),voexsubs).ultimrename(erscope,prescope,mog[t],onlyavailable=onlyavailable,flat=True)
						assert shim.verified#safemode
						comscope = comscope + shim
						t+=1
					break
			else:
				shim = self.variables.data[i].substitute(RenamerObject(erscope),voexsubs).ultimrename(erscope,prescope,mog[t],onlyavailable=onlyavailable)
				for j in shim[0]:#safemode
					print("[[][<<<<<>>>>",j)
					assert j.verified#safemode


				comscope = comscope + shim[0]
				voexsubs = voexsubs + SubsObject(shim[1].unwrapsubs(self.variables.data[i].name))
				jan.append(shim[1])
				t+=1
			erscope = erscope + ScopeIntroducer(self.variables.data[i].name).allvars()

		for j in comscope:#safemode
			print("[[][][][][][[][[][......>>>>",j)
			assert j.verified#safemode
		for j in jan:#safemode
			assert j.verified#safemode
		return (comscope,ObjKindUnionSet(subs=SubsObject(jan,exverified=True),verprot=1,original=self.variables.original) )
	@debugdebug
	def bgroup(self,semscope,mog):
		assert self.verified#safemode
		if type(mog) is ScopeIntroducer: mog = mog.dat
		assert mog != None#safemode

		ErrorObject.takeblame(self)

		# body = self.type.subs.availvariables()
		if len(mog) != len(self.variables.data):
			ErrorObject.fatal("Mechanical error (subside): Wrong number of arguments for unwrap.")

		jan = []
		voexsubs = SubsObject()
		erscope = semscope
		for i in range(len(self.variables.data)):
			for j in self.subs.subs:
				if j.name == self.variables.original.dat[i]:
					assert type(self.variables[i].name) is str#safemode
					yu = copy.copy(j).substitute(erscope,voexsubs)
					yu.name = None
					yu.inherited = True
					jan.append(yu)
					break
			else:
				sfto = self.variables.data[i].substitute(RenamerObject(erscope),voexsubs).bgroup(erscope,mog[i])
				jan.append(sfto)
				erscope = erscope + ScopeIntroducer(self.variables.data[i].name).allvars()
				voexsubs.subs = voexsubs.subs + sfto.unwrapsubs(self.variables.data[i].name)

		return ObjKindUnionSet(subs=SubsObject(jan,exverified=True),verprot=1,original=self.variables.original) 





#-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=







class ObjKindTemplateHolder(ObjKind):
	def __init__(self,src,subs,pos=None,exverified=False):
		assert issubclass(type(src),ObjKind) and type(subs) is SubsObject#safemode
		self.src = src
		self.subs = subs
		transferlines(self,pos)
		self.verified = exverified and self.src.verified and type(self.src) is ObjKindReferenceTree
	def __repr__(self):
		return str(self.src)+"<"+str(self.subs)+">"
	def wide_repr(self,depth):
		return self.src.wide_repr(depth)+"<"+str(self.subs)+">"
	@debugdebug
	def verify(self,scope,carry):
		ErrorObject.takeblame(self)
		if self.verified: return self
		yu = self.src.verify(scope,None)
		if type(yu) is ObjKindTemplateHolder:
			return ObjKindTemplateHolder(src=yu.src,subs=yu.subs+self.subs,pos=self,exverified=True)

		if type(yu) is ObjKindTypeUnion:
			return yu.compactify(scope,self.subs)

		if type(yu) is ObjKindReferenceTree:
			return ObjKindTemplateHolder(src=yu,subs=self.subs,pos=self,exverified=True)

		ErrorObject.fatal("Substitution is only supported on unions.")
	@debugdebug
	def substitute(self,revf,repl):
		return ObjKindTemplateHolder(self.src.substitute(revf,repl),self.subs.substitute(revf,repl),pos=self,exverified=self.verified)
	def refs(self,label):
		return self.src.refs(label) or self.subs.refs(label)
	def equate(self,cno,other):
		if type(other) is not ObjKindTemplateHolder: return False
		return self.src.equate(cno,other.src) and self.subs.equate(cno,other.subs)
class ObjKindReferenceTree(ObjKind):
	def __init__(self,args=None,src=None,name=None,pos=None,verprot=None):
		if args == None:
			self.args = SubsObject()
		elif type(args) is SubsObject:
			self.args = args
		else:
			self.args = SubsObject([IndividualSub(None,ScopeIntroducer([]),args[z],[]) for z in range(len(args))])

		if src != None: assert issubclass(type(src),ObjKind)#safemode
		if name != None: assert type(name) is str or (src != None and type(name) is tuple)#safemode
		self.forgiveLvlup = False
		self.name = name
		self.src = src
		transferlines(self,pos)

		if   verprot == None:
			self.verified = False
		elif verprot == 0:
			self.verified = self.src.verified
		elif verprot == 1:
			self.verified = self.src.verified and self.args.verified
		elif verprot == 2:
			assert self.src == None#safemode
			self.verified = self.args.verified
		else: assert False#safemode

		self.verprot = verprot if self.verified else None
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
	def verify(self,scope,carry):
		ErrorObject.takeblame(self)

		if self.verified: return self
		# 	errors.nonfatal("X")
		if self.src == None and len(self.args) == 0 and self.name == "U":
			if carry.src == None and len(carry.args) == 0 and carry.name == "U":
				return ObjKindReferenceTree(name="U",verprot=2)
		if self.src == None and len(self.args) == 0 and self.name == "~":
			return ObjKindReferenceTree(name="~",verprot=2)
		if self.src != None:
			poc = self.src.verify(scope,None)
			if type(poc) is not ObjKindTypeUnion and type(poc) is not ObjKindUnionSet:
				if type(poc) is ObjKindTemplateHolder: poc=poc.src
				gmo = poc.gentype(scope)
				sgig = None
				if type(gmo) is ObjKindTypeUnion:
					t = gmo.subs.getv(self.name)
					if t != None: sgig = self.arginternal(scope,t,carry)
				return ObjKindReferenceTree(src=poc,args=self.args if sgig==None else sgig,name=self.name,pos=self,verprot=int(sgig!=None))
			blcarry = poc.get(self.name)
			if blcarry == None:
				ErrorObject.fatal("No such property exists or the property exists but was not defined.")
			if len(blcarry.bon) > 0:
				ErrorObject.fatal("The property accessed here is dependently typed and refers to a variable that is unspecified. (Property cannot be used in static context.)")
			t = blcarry.expected
			if t == None:
				ErrorObject.fatal("Unable to infer type for:"+str(self.name))
			nukl,nreu = RenamerObject(scope).integrate(blcarry.si)
			duke = self.arginternal(scope,t,carry)
			mode = blcarry.obj.substitute(nreu,SubsObject(duke.unwrapsubs(nukl,onlyavailable=True)))

			return mode.verify(scope,carry)
		t = scope.get(self.name)
		if t == None:
			ErrorObject.fatal("Referenced variable not in scope:"+self.name)

		snot = self.arginternal(scope,t,carry)
		# snot = self.args#fix this please
		return ObjKindReferenceTree(args=snot,name=self.name,pos=self,verprot=2)
	def gentype(self,scope):
		t = scope.get(self.name)
		if t == None:
			ErrorObject.fatal("Referenced variable not in scope:"+self.name)
		assert self.verified#safemode

		null,nreu = RenamerObject(scope).integrate(t.args.variables.introducer())
		exptyoe = t.type.substitute(nreu,self.args)
		exptyoe = exptyoe.verify(scope,ObjKindReferenceTree(name="U",verprot=2))

		return exptyoe
	@debugdebug
	def arginternal(self,scope,t,carry):

		ErrorObject.takeblame(self)
		if len(self.args) != t.args.lenavail(): ErrorObject.fatal("Wrong argument count.")


		fas = []
		for j in range(len(self.args)):
			mogol = self.args.subs[j]
			marj = t.args.availvariables()[j].args.lenavail()

			if len(self.args.subs[j].si) != marj:
				if self.forgiveLvlup and len(self.args.subs[j].si) < marj:
					mogol = ScopeIntroducer(self.args.subs[j].si.data+[None for n in range(marj-len(self.args.subs[j].si))])
				else:
					ErrorObject.fatal("Wrong number of introduced parameters. expected "+str(marj)+", got "+str(len(self.args.subs[j].si)),self.args.subs[j].obj)
			fas.append(mogol)
		fas = SubsObject(fas) if self.forgiveLvlup else self.args


		# errors.nonfatal("o")

		#more like t.args.compactify(scope,fas,)
		#but you need to remember what was inherited
		snot = fas.postcompact(scope,t.args)
		# snot = SubsObject(fas).precompact(scope,t.args,needscomplete=True).supersubs()


		ErrorObject.takeblame(self)



		# errors.nonfatal(str(carry))
		if carry != None:

			null,nreu = RenamerObject(scope).integrate(t.args.variables.introducer())

			print("o===-=-=->",snot)
			exptyoe = t.type.substitute(nreu,SubsObject(snot.unwrapsubs(null)))
			exptyoe = exptyoe.verify(scope,ObjKindReferenceTree(name="U",verprot=2))

			def recurstep(exptyoe):
				valids = 0
				if exptyoe.caststo(CrossNameObject(),carry):
					valids += 1
				elif type(exptyoe) is ObjKindTypeUnion:
					for j in exptyoe.subs.variables.data:
						if j.args.lenavail() == 0:
							valids += recurstep(j.type)
				return valids

			valids = recurstep(exptyoe)

			if valids > 1:
				ErrorObject.nonfatal("unable to infer which member to extract from composite type")
			if valids == 0:
				ErrorObject.nonfatal(str(exptyoe)+" =/= "+str(carry))


		return snot
	@debugdebug
	def substitute(self,revf,repl):
		# if len(revf.data) == 0 and len(repl) == 0: return self
		yobi = self.args.substitute(revf,repl)
		if self.src != None:
			return ObjKindReferenceTree(args=yobi,src=self.src.substitute(revf,repl),name=self.name,pos=self,verprot=self.verprot)
		i = repl.get(revf[self.name],None)
		if i == None:
			return ObjKindReferenceTree(args=yobi,name=revf[self.name],pos=self,verprot=self.verprot)

		tsi,ghn = revf.alternate().integrate(i.si)

		gam = i.obj.substitute(ghn,SubsObject(yobi.unwrapsubs(tsi,None,onlyavailable=True)))
		if type(gam) is ObjKindUnionSet:
			if gam.verprot == 0:
				gam = copy.copy(gam)
				gam.verified = False
				gam.verprot = None
		if not self.verified:
			gam.verified = False
		return gam
	def render(self,scope,carry):
		assert self.verified#safemode
		assert self.src==None#safemode

		wak = self.args.render(scope)
		return Statement(args=[i[1] for i in wak],name=self.name,lvlup=[i[0] for i in wak])

	def equate(self,cno,other):
		if type(other) is not ObjKindReferenceTree: return False
		if not cno.equivalen(self.name,other.name): return False
		if not self.args.equate(cno,other.args): return False
		if self.src == None and other.src == None: return True
		if self.src == None or other.src == None: return False
		return self.src.equate(cno,other.src)
	def refs(self,label):
		if self.src == None and self.name == label: return True
		if self.args.refs(label): return True
		if self.src != None and self.src.refs(label): return True
		return False
class ObjKindUnionSet(ObjKind):
	def __init__(self,subs=None,pos=None,verprot=None,original=None):
		self.subs = SubsObject() if subs == None else subs if type(subs) is SubsObject else SubsObject(subs)
		transferlines(self,pos)
		# self.inherited = [] if inherited == None else inherited

		self.original = original

		if   verprot == None:
			self.verified = False
		elif verprot == 0:
			self.verified = True
		elif verprot == 1:
			self.verified = self.subs.verified
		else: assert False#safemode
		self.verprot = verprot if self.verified else None
		if self.verified: assert self.original != None
	def __repr__(self):
		return "("+str(self.subs)+")"
	def wide_repr(self,depth):
		return "("+self.subs.wide_repr(depth+1)+"\n"+"\t"*depth+")"
	@debugdebug
	def verify(self,scope,carry):
		ErrorObject.takeblame(self)
		if self.verprot == 0 and carry == None or self.verprot == 1: return self
		# if self.verified and self.completed: return self
		if carry == None:
			ewgross = copy.copy(self)
			ewgross.verified = True
			ewgross.verprot = 0
			return ewgross

		if type(carry) is not ObjKindTypeUnion:
			ErrorObject.fatal("Can't pair keyword arguments to static type.")

		return ObjKindUnionSet(subs=self.subs.postcompact(scope,carry.subs),pos=self,verprot=1,original=carry.subs.variables.original)
	@debugdebug
	def substitute(self,revf,repl):
		# if len(revf.data) == 0 and len(repl) == 0: return self
		return ObjKindUnionSet(subs=self.subs.substitute(revf,repl),pos=self,verprot=self.verprot,original=self.original)
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry):
		union

	def get(self,lab):
		return self.subs.unwrapsubs(self.original).get(lab)


	def equate(self,cno,other):
		if type(other) is not ObjKindUnionSet: return False
		return self.subs.equate(cno,other.subs)
class ObjKindTypeUnion(ObjKind):
	def __init__(self,parsed=None,subs=None,variables=None,pos=None,exverified=False):
		transferlines(self,pos)
		if type(subs) is DualSubs:
			assert variables == None#safemode
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
	def verify(self,scope,carry):
		ErrorObject.takeblame(self)
		if self.verified: return self
		return ObjKindTypeUnion(subs=self.subs.verify(scope),pos=self,exverified=True)
	@debugdebug
	def compactify(self,scope,subs):
		return ObjKindTypeUnion(subs=self.subs.compactify(scope,subs),pos=self,exverified=True)
	@debugdebug
	def substitute(self,revf,subs):
		# if len(revf.data) == 0 and len(subs) == 0: return self
		return ObjKindTypeUnion(subs=self.subs.substitute(revf,subs),pos=self,exverified=self.verified)
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry):
		oafdjosidfjoasidf

	def get(self,lab):
		return self.subs.get(lab)

	def equate(self,cno,other):
		if type(other) is not ObjKindTypeUnion: return False
		return self.subs.equate(cno,other.subs)
	def caststo(self,cno,other):
		if type(other) is not ObjKindTypeUnion: return False
		return self.subs.caststo(cno,other.subs)


oneoff = True
totruntime = 0


class ObjStrategy:
	def __init__(self,args=None,ty=None,name=None,pos=None,exverified=False):
		if type(name) is ScopeIntroducer: name = name.dat
		self.args = DualSubs(StratSeries(),exverified=True) if args == None else DualSubs(StratSeries(args)) if isinstance(args,list) else args
		self.name = name
		self.type = ty
		assert self.name == None or type(self.name) is str or type(self.name) is list#safemode
		transferlines(self,pos)
		assert issubclass(type(self.type),ObjKind)#safemode
		assert type(self.args) is DualSubs#safemode
		self.verified = exverified and self.type.verified and self.args.verified
	def __repr__(self):
		if len(self.args.variables.data) != 0:
			if self.name != None: return "["+str(self.args)+"]"+str(self.name)+":"+str(self.type)
			else: return "["+str(self.args)+"]"+str(self.type)
		else:
			if self.name != None: return str(self.name)+":"+str(self.type)
			else: return str(self.type)
	def refsany(self,si):
		def minjcontains(j):
			if isinstance(j,list):
				return any(minjcontains(o) for o in j)
			return self.refs(j)
		return minjcontains(si.dat)
	@debugdebug
	def verify(self,scope):
		global oneoff
		sarg = oneoff
		oneoff = False

		ErrorObject.takeblame(self)
		if self.verified: return self

		if sarg:print("I MEAN ALRIGHT")
		if sarg:prestart = time.time()
		verargs = self.args.verify(scope)
		if sarg:start = time.time()

		# sresressres = None
		# if not sarg:
		sresressres = ObjStrategy(
			args=verargs,
			ty=self.type.verify(scope+verargs.variables,ObjKindReferenceTree(name="U",verprot=2)),
			name=self.name,
			pos=self,
			exverified=True
		)
		if sarg:end = time.time()
		if sarg:print("TIME TAKEN: ",start - prestart)
		if sarg:print("TIME TAKEN: ",end - start)

		return sresressres
	@debugdebug
	def substitute(self,revf,repl):
		if len(revf.data) == 0 and len(repl) == 0: return self
		null,mmn = revf.integrate(self.args.variables.introducer())
		return ObjStrategy(args=self.args.substitute(revf,repl),ty=self.type.substitute(mmn,repl),name=self.name,pos=self,exverified=self.verified)
	def refs(self,label):
		if self.args.refs(label): return True
		return not self.args.variables.introducer().contains(label) and self.type.refs(label)
	def surfacerename(self,newname):
		if newname == self.name: return self
		assert newname == None or type(newname) is str#safemode
		y = copy.copy(self)
		y.name = newname
		return y
	@debugdebug
	def split(self,semscope):
		if type(self.name) is str: return [self]
		uoiu = self.ultimrename(semscope,DualSubs(StratSeries(),exverified=True),self.name,flat=True)

		return uoiu
	@debugdebug
	def bgroup(self,semscope,mog):
		assert self.verified#safemode
		assert mog != None#safemode
		assert self.name != None#safemode
		def arbirow(depth,length):
			return ScopeIntroducer([str(depth)+":"+str(h) for h in range(length)])
		def minjcontains(j):
			if isinstance(j,list):
				return max(minjcontains(p) for p in j)
			sn = j.split(":")
			if len(sn) == 1: return 0
			try: return int(sn[0])+1
			except: return 0
		def simconvert(k,depth,sera=0):
			assert k.verified#safemode
			po=[]
			zardu = k.args.availvariables()
			for i in range(len(zardu)):
				nname = (str(depth)+":"+str(i-sera)) if i>=sera else zardu[i].name
				jjak = (depth+1) if i>=sera else minjcontains(zardu[i].name)

				ja = arbirow(jjak,len(zardu[i].args.data))
				jalarg = ObjKindReferenceTree(name=nname,args=simconvert(zardu[i],jjak),verprot=2)
				assert jalarg.verified#safemode
				po.append(IndividualSub(zardu[i].name,ja,jalarg,[],zardu[i],exverified=True))
				assert po[-1].verified#safemode
			return SubsObject(po,exverified=True)
		ErrorObject.takeblame(self)
		# momam = self.substitute(RenamerObject(semscope+prescope.variables.introducer().allvars()),exsubs)
		if type(mog) is str:
			nsfar = minjcontains(mog)
			moh = ObjKindReferenceTree(name=mog,args=simconvert(self,nsfar),verprot=2)#scrutinize sera
			return IndividualSub(mog,arbirow(nsfar,self.args.lenavail()),moh,[],self,exverified=True)

		if type(self.type) is not ObjKindTypeUnion:
			ErrorObject.fatal("Mechanical error (subside): Non-unionset unwrapped in given paramter for eval. mog:"+str(mog)+" ,self: "+str(self))

		jan = self.type.subs.bgroup(semscope + self.args.variables.introducer().allvars(),mog)
		return IndividualSub(None,ScopeIntroducer([k.name for k in self.args.availvariables()]),jan,[],self,exverified=True)
	@debugdebug
	def ultimrename(self,semscope,prescope,mog,flat=False,onlyavailable=False):
		assert prescope.verified#safemode
		assert self.verified#safemode
		if type(mog) is ScopeIntroducer: mog = mog.dat
		assert mog != None#safemode
		assert self.name != None#safemode
		ErrorObject.takeblame(self)
		# momam = self.substitute(RenamerObject(semscope+prescope.variables.introducer().allvars()),exsubs)
		if type(mog) is str:
			mostrat = ObjStrategy(name=mog,ty=self.type,args=prescope+self.args,exverified=True)

			assert mostrat.verified#safemode
			if flat: return [mostrat]
			return ([mostrat],self.bgroup(semscope,mog))

		if type(self.type) is not ObjKindTypeUnion:
			ErrorObject.fatal("Mechanical error (subside): Non-unionset unwrapped in given paramter for eval. mog:"+str(mog)+" ,self: "+str(self))
		zador = self.type.subs.ultimrename(semscope+self.args.variables.introducer().allvars(),prescope+self.args,mog)
		if flat: return zador[0]
		# return zador

		zador = (zador[0],IndividualSub(None,ScopeIntroducer([k.name for k in self.args.availvariables()]),ObjKindUnionSet(subs=zador[1],exverified=True),[],self,exverified=True))

		for y in zador[0]:#safemode
			assert y.verified#safemode
		assert zador[1].verified#safemode
		return zador
		# return (zador[0],zador[1].unitreformat(semscope,momam,self.variables.introducer(),self.name,onlyavailable=onlyavailable))
	@debugdebug
	def reformat(self,scope,mog):
		zador = self.args.ultimrename([k.name for k in scope.flat],DualSubs(StratSeries(),exverified=True),mog,onlyavailable=True)
		sarl = zador[1].subs.unwrapsubs(self.args.variables.introducer())
		sja = self.type.substitute(RenamerObject([k.name for k in scope.flat]+self.args.variables.introducer().allvars()),SubsObject(sarl))
		goreturn = ObjStrategy(name=self.name,ty=sja,args=DualSubs(StratSeries(zador[0],zador[0]))).verify(scope)
		assert goreturn.verified#safemode
		return goreturn
	def equate(self,cno,other):
		if not self.args.equate(cno,other.args): return False
		return self.type.equate(other.sertequiv(self.introducer(),other.introducer()),other.type)





# you still need unwrapsubs to respect the () singleton

# bgroup is a->b, should types be in terms of a or b



# each bgroup and all that... identify how many arguments each mog-strat shuold have


#	code form
#review comments,prints,and assertions, and try/catches, and raises, and returns
#	take this serieously- more of the todo list is floating in the doc
#check all returns and args to see if its the wrapping class or just the internal, and establish some kind of convention
#you could do stuff like overriding lists to make encapsulators look nicer... probably in another version



#	verification
#do a statement verify after
#unwrapsubs erases slamsubs and so does substitution -> add a verification endpoint from where the data leaves the context.



#   possible features
#implicit cast may also allow extra data (as in variables) to be stripped away.
#make strategy arguments into a dualsubs object
#make S satisfy {S} both positionally and when named; you can still have single-sub tuples...
#operator overloading
#add ->()



#verify twice inherited conflict>????????????? check it out in postcompact




#   possible bugs
#double check that ultimrename doesn't take you from a no scope occlusion situation to a scope occlusion situation.
#stratseries refs doesn't occlude any scope- is this normal?
#you do this pattern where you concatenate to subs... just make sure you dont get a pass by reference problem.
#expected doesn't really work with bon. review every usage
#individualsub substitute needs to handle expected, but it doesn't censor bon variables...
#what if you're renaming a strategy to an SI that the strategy accidently references?
#stratseries may need exverified back../.
#substitution on stratseries can leave it with a flat representation but not be verified...




