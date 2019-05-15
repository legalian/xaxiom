
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
	return F
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
		# for x in range(len(self.s)):#safemode
			# for y in range(x):#safemode
				# assert self.s[x]!=self.s[y]#safemode


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
			# assert len(g) == 1 or len(g) == 2#safemode
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
	# def asrenamer(self):
	# 	return RenamerObject(dict(self.data))
	# def __getitem__(self,key):
	# 	return self.asrenamer()[key]
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
	def __init__(self,rer=None,tac=None):
		self.rer = [] if rer == None else rer
		self.tac = [] if tac == None else tac
		self.blame = None
	def takeblame(self,obk):
		self.blame = obk
	def nonfatal(self,err,obk=None):
		# assert type(err) is str#safemode
		if obk == None:
			# assert self.blame != None#safemode
			self.rer.append((err,self.blame,self.tac))
		else:
			self.rer.append((err,obk,self.tac))
	def error(self,err,obk=None):
		# assert type(err) is str#safemode
		if obk == None:
			# assert self.blame != None#safemode
			return ErrorObject([(err,self.blame,self.tac)])
		else:
			return ErrorObject([(err,obk,self.tac)])
	def tack(self):
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
		# assert type(label) is str#safemode
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
	def __init__(self,name,si,obj,bon,expected=None,exverified=False):
		# assert type(name) is str or name == None#safemode
		# assert type(expected) is ObjStrategy or expected == None#safemode
		# assert type(si) is ScopeIntroducer#safemode
		# assert issubclass(type(obj),ObjKind)#safemode


		self.name = name
		self.si = si
		self.obj = obj
		self.bon = bon if type(bon) is ScopeSelectionObject else ScopeSelectionObject(bon)
		self.expected = expected

		self.verified = exverified and (self.expected == None or self.expected.verified) and self.obj.verified
		# if self.expected != None:#safemode
			# assert if len(si.dat) == len(expected.args.data):#safemode
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

		uhf = self.obj.substitute(mmn2,repl)

		# jae = None if self.expected == None else self.expected.substitute(revf,repl) this substitute doesn't work wor

		return IndividualSub(self.name,nsi,uhf,nbon,None,exverified=self.verified)




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
	def unwrapsubs(self,mog,bobo=None,prep=None):
		if prep == None: prep = []
		def internalsubsmake(mog,trail,prep):
			if isinstance(mog,list):
				return [i for f in range(len(mog)) for i in internalsubsmake(mog[f],trail+[(f,len(mog))],prep)]
			jog = self.obj
			for s in trail:
				jog = ObjKindReferenceTree(src=jog,name=s,verprot=0)
			return [IndividualSub(mog,ScopeIntroducer(prep+self.si.dat),jog,[] if bobo == None else bobo,exverified=True)]
		if isinstance(mog,list):
			if type(self.obj) is not ObjKindUnionSet:
				return internalsubsmake(mog,[],prep+self.si.dat)
			else:
				return self.obj.subs.unwrapsubs(mog,bobo=bobo,prep=prep+self.si.dat)
		else:
			return [IndividualSub(mog,ScopeIntroducer(prep+self.si.dat),self.obj,[] if bobo == None else bobo,exverified=True)]



class SubsObject:
	def __init__(self,data=None,exverified=False):
		# if data != None:#safemode
			# for k in data: assert type(k) is IndividualSub#safemode
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
	def unwrapsubs(self,mog,bobo=None,prep=None):
		if type(mog) is ScopeIntroducer: mog = mog.dat

		# assert type(mog) is not str#safemode
		# assert len(mog) == len(self)#safemode
		return [i for f in range(len(mog)) for i in self.subs[f].unwrapsubs(mog[f],bobo=bobo,prep=prep)]



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
			if label[1]!=len(self.subs): raise errors.error("mechanical: Wrong number of introduced parameters.")
			return self.subs[label]
		for t in reversed(self.subs):
			if t.name == label:
				return t
		return None


	def render(self,scope):
		# for zal in self.subs:#safemode
			# assert len(zal.bon) == 0#safemode
		return [(zal.si.allvars(),zal.obj.verify(scope+zal.expected.args,zal.expected.type)) for zal in self.subs]

	@debugdebug
	def precompact(self,scope,cars,errors,needscomplete=False):
		# assert type(cars) is StratSeries#safemode
		sortversion = []
		i=0
		flatvars = cars.original.allvars()
		while i<len(self.subs):
			if i>=len(cars.original.dat): raise errors.error("Too many arguments.")
			if self.subs[i].name != None: break
			sortversion = sortversion + self.subs[i].unwrapsubs(cars.original.dat[i])
			i+=1
		spoken = [False]*(len(self.subs)-i)
		for d in range(len(sortversion),len(cars.original.allvars())):
			for k in range(i,len(self.subs)):
				if not spoken[k-i] and self.subs[k].name == flatvars[d]:
					sortversion.append(self.subs[k])
					spoken[k-i] = True
					break
			else:
				if needscomplete:
					if flatvars[d]==None: raise errors.error("Missing positional argument.")
					else: raise errors.error("Missing named argument: "+str(flatvars[d]))
				else: sortversion.append(None)
		for j in range(len(self.subs)-i):
			if self.subs[j+i].name == None:
				raise errors.error("Positional argument cannot come after named argument.")
		for j in range(len(self.subs)-i):
			if not spoken[j]:
				raise errors.error("Unknown argument specified: "+str(self.subs[j+i].name))
		sofar = []
		for em in sortversion:
			if em == None: continue
			for check in em.bon.bon():
				if check not in sofar and em.obj.refs(check) and not em.si.contains(check):
					raise errors.error("The usage of the following variable violates the well-ordering property: "+check)
			sofar.append(em.name)

		# assert len(sortversion) == len(cars.flat)#safemode
		# assert len(cars.original.allvars()) == len(cars.flat)#safemode

		nhead = 0

		simpsubs = []
		flatsubs = []
		zndata = []
		znflat = []

		mmn = RenamerObject(scope)

		for z in range(len(cars.data)):
			# for x in znflat:#safemode
				# assert type(x.name) is str#safemode
			pscope = scope+StratSeries(zndata,znflat,original=ScopeIntroducer(cars.original.dat[:z]))
			nname,mmn2 = mmn.integrate(ScopeIntroducer(cars.data[z].name))
			nname = nname.dat

			zaku = cars.data[z].substitute(mmn,SubsObject(flatsubs)).surfacerename(nname)

			if type(cars.data[z].name) is str:
				if sortversion[nhead] != None:
					nsi,lmmn = mmn.temper(pscope.original.allvars(),sortversion[nhead].bon).integrate(sortversion[nhead].si)
					strud = zaku.reformat(pscope,nsi,errors)
					nobj = sortversion[nhead].obj.substitute(lmmn,SubsObject(flatsubs)).verify(pscope+strud.args,strud.type,errors)
					
					orjambo = []
					jambo = []

					for jam in range(len(znflat)):
						if zaku.refs(znflat[jam].name) or nobj.refs(znflat[jam].name):
							jambo.append(znflat[jam].name)
							orjambo.append((cars.original.dat[jam],znflat[jam].name))


					simpsubs.append(IndividualSub(cars.data[z].name,nsi,nobj,orjambo,zaku,exverified=True))
					flatsubs.append(IndividualSub(nname,nsi,nobj,jambo,zaku,exverified=True))
				zndata.append(zaku)
				znflat.append(zaku)

				# for x in znflat:#safemode
					# assert type(x.name) is str#safemode
				nhead += 1
				mmn = mmn2
			else:
				snscope = pscope+zaku.args
				sara = len(ScopeIntroducer(zaku.name).allvars())
				akar = []
				vlode = []
				for k in range(sara):
					nlorname,mmn2 = mmn.integrate(ScopeIntroducer(cars.flat[nhead+k].name))
					nlorname = nlorname.dat
					hzaku = cars.flat[nhead+k].substitute(mmn,SubsObject(flatsubs)).surfacerename(nlorname)

					if sortversion[nhead+k] != None:
						nsi,lmmn = mmn.temper(pscope.original.allvars(),sortversion[nhead+k].bon).integrate(sortversion[nhead+k].si)
						zolt = []
						if len(sortversion[nhead+k].si.dat)<len(zaku.args.data):
							raise errors.error("Not enough introduced parameters for this pattern.")
						for e in range(len(zaku.args.data)):
							vog = copy.copy(zaku.args.data[e])
							vog.name = sortversion[nhead+k].si.dat[e]
							zolt = zolt + vog.ultimrename(snscope,StratSeries(),SubsObject(),mog,[],errors)[1].subs#<----- can add subs here you know
						ansi = ScopeIntroducer(nsi.dat[len(zaku.args.data):])
						nobj = sortversion[nhead+k].obj.substitute(lmmn,SubsObject(flatsubs+zolt))


						# orjambo = []
						jambo = []
						for jam in vlode:
							if hzaku.refs(jam) or nobj.refs(jam):
								jambo.append(jam)
								# orjambo.append(<><><>)

						akar.append(IndividualSub(nlorname,ansi,nobj,jambo))#<--- nlorname,jambo needs to be changed here.
						flatsubs.append(IndividualSub(nlorname,nsi,nobj,jambo,hzaku,exverified=True))


						vlode.append(nlorname)

						znflat.append(hzaku)
						# for x in znflat:#safemode
							# assert type(x.name) is str#safemode

					mmn = mmn2

				#zaku.type.subs.variables ???????

				#don't specify a type here- you don't need the result to be verified.

				# <><><><><><>

				#should it really be zaku.name or should it be originals[i] or...?
				shot = SubsObject(akar).reformat(
					[k.name for k in snscope.flat],
					zaku.type.subs.variables.flat,
					zaku.name,
					zaku.type.subs.variables.original,
					errors)
				# assert False#do you need to specify bonargs=zaku.args????????? no i dont think so

				zot = zaku.type.subs.compactify(snscope,shot,errors)

				zndata.append(zaku)

				nhead += sara



		zalog = DualSubs(StratSeries(zndata,znflat,original=cars.original),SubsObject(simpsubs,exverified=True),exverified=True)
		# assert zalog.verified#safemode
		return zalog






	@debugdebug
	def unitreformat(self,semscope,body,sifrom,sito,errors,bonargs=None):
		# if bonargs == None: bonargs = StratSeries()
		def lcount(shar):
			if type(shar) is ObjKindReferenceTree:
				if shar.src != None: return lcount(shar.src)
				return [shar.name]
			return [k for i in shar.subs.subs for k in lcount(i.obj)]

		for i in self.subs:
			if len(i.bon) != 0:
				raise errors.error("stub")
		if type(sifrom) is ScopeIntroducer: sifrom = sifrom.dat
		if type(sito) is ScopeIntroducer: sito = sito.dat

		jan = []
		erscope = semscope

		build = body.bgroup(semscope,SubsObject(),StratSeries(),sifrom,[],errors)

		build = build.unwrapsubs(sito)#,prep=[o.name for o in bonargs.data]
		# jar = []
		for sa in build:
			ll = lcount(sa.obj)
			l = [i in [k.name for k in self.subs] for i in ll]
			if all(l):
				#this seems super sketchy...... review the below line
				jan.append(sa.substitute(RenamerObject(semscope+ScopeIntroducer(ll).allvars()),self.only(ScopeIntroducer(ll))))
			elif any(l):
				raise errors.error("illegal substitution pattern encountered: grouping an existant and nonexistant substitution.")

		return SubsObject(jan)





	@debugdebug
	def reformat(self,semscope,body,sifrom,sito,errors):
		def lcount(shar):
			if type(shar) is ObjKindReferenceTree:
				if shar.src != None: return lcount(shar.src)
				return [shar.name]
			return [k for i in shar.subs.subs for k in lcount(i.obj)]

		for i in self.subs:
			if len(i.bon) != 0:
				raise errors.error("stub")
		if type(sifrom) is ScopeIntroducer: sifrom = sifrom.dat
		if type(sito) is ScopeIntroducer: sito = sito.dat

		# if type(sito) is str: assert False#safemode
		# if type(sifrom) is str: assert False#safemode


		jan = []
		voexsubs = SubsObject()
		erscope = semscope
		for i in range(len(body)):

			build = body[i].bgroup(erscope,voexsubs,StratSeries(),sifrom[i],[],errors)

			build = build.unwrapsubs(sito[i])#
			# jar = []
			for sa in build:
				ll = lcount(sa.obj)
				l = [i in [k.name for k in self.subs] for i in ll]
				if all(l):
					#this seems super sketchy...... review the below line
					jan.append(sa.substitute(RenamerObject(erscope+ScopeIntroducer(ll).allvars()),self.only(ScopeIntroducer(ll))))
				elif any(l):
					raise errors.error("illegal substitution pattern encountered: grouping an existant and nonexistant substitution.")
			shim = body[i].ultimrename(erscope,voexsubs,StratSeries(),sifrom[i],[],errors)
			voexsubs = voexsubs + shim[1]
			erscope = erscope + ScopeIntroducer(body[i].name).allvars()


		return SubsObject(jan)



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
		# for k in self.data: assert type(k) is ObjStrategy#safemode
		self.verified = all(k.verified for k in self.data) and flatdata != None

		self.flat = flatdata
		# if self.flat != None:#safemode
			# for k in self.flat:#safemode
				# assert type(k) is ObjStrategy#safemode
				# assert type(k.name) is str#safemode



		# assert (self.flat == None) != (self.verified) #safemode
		# for h in range(len(self.data)):#safemode
			# for g in self.data[:h]:#safemode
				# if g.name != None:#safemode
					# assert g.name != self.data[h].name#safemode
		# if self.flat != None:#safemode
			# for j in self.flat: assert j.verified#safemode
			# for h in range(len(self.flat)):#safemode
				# for g in self.flat[:h]:#safemode
					# if g.name != None:#safemode
						# assert g.name != self.flat[h].name#safemode


		self.original = self.introducer() if original == None else original

	def __repr__(self):
		return ",".join([str(i) for i in self.data])
	def wide_repr(self,depth):
		return (",\n"+"\t"*depth).join([str(i) for i in self.data])
	@debugdebug
	def verify(self,scope,errors):
		if self.verified: return self
		zvn = []
		zn = []
		mmn = RenamerObject(scope)
		for k in range(len(self.data)):
			nm,nmmn = mmn.integrate(ScopeIntroducer(self.data[k].name))
			pscope = StratSeries(zn,zvn,original=ScopeIntroducer(self.original.dat[:k]))
			p = self.data[k].surfacerename(nm.dat).substitute(mmn,SubsObject()).verify(scope+pscope,errors)
			mmn=nmmn
			zn.append(p)
			zvn = zvn + p.split([k.name for k in scope.flat]+[k.name for k in zvn],errors)
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
		# if label != None: assert type(label) is str#safemode
		for k in self.data:
			if k.refs(label): return True
			if k.name == label: return False
		return False
	def get(self,label,errors):
		if type(label) is tuple:
			if label[1]!=len(self.data): raise errors.error("mechanical: Wrong number of introduced parameters.")
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
	def __init__(self,variables,subs=None,sphsubs=None,exverified=False):
		# assert type(variables) is StratSeries#safemode
		# if subs != None: assert type(subs) is SubsObject#safemode
		self.variables = variables
		self.subs = subs if subs != None else SubsObject()

		self.sphsubs = sphsubs

		# for k in self.subs.subs:#safemode
			# for j in k.bon.bon():#safemode
				# if not ScopeIntroducer(self.variables.original).contains(j):#safemode
					# assert False#safemode



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
	def verify(self,scope,errors,needscomplete=False):
		if self.verified: return self

		varver = self.variables.verify(scope,errors)

		if self.sphsubs != None:
			she = []
			for o in self.sphsubs:
				he = IndividualSub(None,o[1],o[2],[])
				she = she + he.unwrapsubs(o[0],bobo=o[3])
			shash = SubsObject(she).precompact(scope,varver,errors,needscomplete=needscomplete)
		else:
			shash = self.subs.precompact(scope,varver,errors,needscomplete=needscomplete)
		# shash.bon = self.bon.rename(shash.bon.asrenamer())
		return shash
	@debugdebug
	def compactify(self,scope,subs,errors,needscomplete=False):
		# assert self.verified#safemode
		return DualSubs(self.variables,subs+self.subs).verify(scope,errors,needscomplete=needscomplete)

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

	def supersubs(self):
		untrance = {}
		# assert len(self.variables.original.dat) == len(self.variables.data)#safemode
		for e in range(len(self.variables.original.dat)):
			untrance[self.variables.original.dat[e]] = self.variables.data[e].name

		yak = []
		for j in self.subs.subs:
			kp = copy.copy(j)
			kp.name = untrance.get(kp.name,None)
			# assert len(kp.bon) == 0#safemode
			yak.append(kp)
		for p in self.variables.data:
			flatvars = ScopeIntroducer(p.name).allvars()
			if type(p.name) is not str and type(p.type) is ObjKindTypeUnion:
				zel = p.type.subs.supersubs()
				for o in range(len(zel)):
					kp = copy.copy(zel[o])
					kp.name = flatvars[o]
					kp.si = ScopeIntroducer(p.args.introducer().dat+kp.si.dat)
					yak.append(kp)

		return SubsObject(yak,exverified=True)

	def getv(self,name,errors):
		return self.variables.get(name,errors)


	def equate(self,cno,other):
		vno = cno.sertequiv(self.variables.original,other.variables.original)
		return self.variables.equate(cno,other.variables) and self.subs.equate(vno,other.subs)
	def caststo(self,cno,other):
		vno = cno.sertequiv(self.variables.original,other.variables.original)
		return self.variables.equate(cno,other.variables) and self.subs.caststo(vno,other.subs)

	def availvariables(self):
		# assert self.verified#safemode

		# for k in range(len(self.variables.data)):#safemode
			# if self.variables.data[k].name in [j.name for j in self.subs.subs]:#safemode
				# for o in self.variables.data[k+1:]:#safemode
					# if o.refs(self.variables[k].name):#safemode
						# assert False#safemode
		res = []
		for t in range(len(self.variables.data)):
			for j in self.subs.subs:
				if j.name == self.original.dat[t]: break
			else:
				res.append(self.variables.data[t])
		return res





#-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=







class ObjKindTemplateHolder(ObjKind):
	def __init__(self,src,subs,pos=None,exverified=False):
		# assert issubclass(type(src),ObjKind) and type(subs) is SubsObject#safemode
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
			return ObjKindTemplateHolder(src=yu.src,subs=yu.subs+self.subs,pos=self,exverified=True)

		if type(yu) is ObjKindTypeUnion:
			return yu.compactify(scope,self.subs,errors)

		if type(yu) is ObjKindReferenceTree:
			return ObjKindTemplateHolder(src=yu,subs=self.subs,pos=self,exverified=True)

		raise errors.error("Substitution is only supported on unions.")
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

		# if src != None: assert issubclass(type(src),ObjKind)#safemode
		# if name != None: assert type(name) is str or (src != None and type(name) is tuple)#safemode
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
			# assert self.src == None#safemode
			self.verified = self.args.verified
		# else: assert False#safemode

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
	def verify(self,scope,carry,errors):
		errors.takeblame(self)

		if self.verified: return self
		# 	errors.nonfatal("X")
		if self.src == None and len(self.args) == 0 and self.name == "U":
			if carry.src == None and len(carry.args) == 0 and carry.name == "U":
				return ObjKindReferenceTree(name="U",verprot=2)
		if self.src == None and len(self.args) == 0 and self.name == "~":
			return ObjKindReferenceTree(name="~",verprot=2)
		if self.src != None:
			poc = self.src.verify(scope,None,errors)
			if type(poc) is not ObjKindTypeUnion and type(poc) is not ObjKindUnionSet:
				if type(poc) is ObjKindTemplateHolder: poc=poc.src
				gmo = poc.gentype(scope,errors)
				sgig = None
				if type(gmo) is ObjKindTypeUnion:
					t = gmo.subs.getv(self.name,errors)
					if t != None: sgig = self.arginternal(scope,t,carry,errors)
				return ObjKindReferenceTree(src=poc,args=self.args if sgig==None else sgig,name=self.name,pos=self,verprot=int(sgig!=None))
			blcarry = poc.subs.get(self.name,errors)
			if blcarry == None:
				raise errors.error("No such property exists or the property exists but was not defined.")
			if len(blcarry.bon) > 0:
				raise errors.error("The property accessed here is dependently typed and refers to a variable that is unspecified. (Property cannot be used in static context.)")
			t = blcarry.expected
			if t == None:
				raise errors.error("Unable to infer type for:"+str(self.name))
			nukl,nreu = RenamerObject(scope).integrate(blcarry.si)
			duke = self.arginternal(scope,t,carry,errors,restr=nukl)

			mode = blcarry.obj.substitute(nreu,duke)



			return mode.verify(scope,carry,errors.tack())
		t = scope.get(self.name,errors)
		if t == None:
			raise errors.error("Referenced variable not in scope:"+self.name)

		snot = self.arginternal(scope,t,carry,errors)
		# snot = self.args#fix this please
		return ObjKindReferenceTree(args=snot,name=self.name,pos=self,verprot=2)
	def gentype(self,scope,errors):
		t = scope.get(self.name,errors)
		if t == None:
			raise errors.error("Referenced variable not in scope:"+self.name)


		null,nreu = RenamerObject(scope).integrate(t.args.introducer())
		exptyoe = t.type.substitute(nreu,self.args)
		exptyoe = exptyoe.verify(scope,ObjKindReferenceTree(name="U",verprot=2),errors.tack())

		return exptyoe
	@debugdebug
	def arginternal(self,scope,t,carry,errors,restr=None):

		errors.takeblame(self)
		if len(self.args) != len(t.args.data): raise errors.error("Wrong argument count.")


		fas = []
		for j in range(len(self.args)):
			mogol = self.args.subs[j]
			if len(self.args.subs[j].si) != len(t.args.data[j].args.data):
				if self.forgiveLvlup and len(self.args.subs[j].si) < len(t.args.data[j].args.data):
					mogol = ScopeIntroducer(self.args.subs[j].si.data+[None for n in range(len(t.args.data[j].args.data)-len(self.args.subs[j].si))])
				else:
					raise errors.error("Wrong number of introduced parameters. expected "+str(len(t.args.data[j].args.data))+", got "+str(len(self.args.subs[j].si)),self.args.subs[j].obj)
			fas.append(mogol)



		# errors.nonfatal("o")
		snot = SubsObject(fas).precompact(scope,t.args,errors,needscomplete=True).supersubs()

		errors.takeblame(self)




		# errors.nonfatal(str(carry))
		if carry != None:
			null,nreu = RenamerObject(scope).integrate(t.args.introducer())
			exptyoe = t.type.substitute(nreu,snot)
			exptyoe = exptyoe.verify(scope,ObjKindReferenceTree(name="U",verprot=2),errors.tack())

			def recurstep(exptyoe):
				valids = 0
				if exptyoe.caststo(CrossNameObject(),carry):
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



		if restr != None:
			return snot.reformat([l.name for l in scope],t.args,t.args.introducer,restr,errors)
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

		gam = i.obj.substitute(ghn,SubsObject(yobi.unwrapsubs(tsi)))
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
	def __init__(self,subs=None,inherited=None,pos=None,verprot=None):
		self.subs = SubsObject() if subs == None else subs if type(subs) is SubsObject else SubsObject(subs)
		transferlines(self,pos)
		self.inherited = [] if inherited == None else inherited

		if   verprot == None:
			self.verified = False
		elif verprot == 0:
			self.verified = True
		elif verprot == 1:
			self.verified = self.subs.verified
		# else: assert False#safemode
		self.verprot = verprot if self.verified else None
	def __repr__(self):
		return "("+str(self.subs)+")"
	def wide_repr(self,depth):
		return "("+self.subs.wide_repr(depth+1)+"\n"+"\t"*depth+")"
	@debugdebug
	def verify(self,scope,carry,errors):
		errors.takeblame(self)
		if self.verprot == 0 and carry == None or self.verprot == 1: return self
		# if self.verified and self.completed: return self
		if carry == None:
			ewgross = copy.copy(self)
			ewgross.verified = True
			ewgross.verprot = 0
			return ewgross

		if type(carry) is not ObjKindTypeUnion:
			raise errors.error("Can't pair keyword arguments to static type.")




		return ObjKindUnionSet(subs=carry.compactify(scope,self.subs.without(ScopeIntroducer(self.inherited)),errors,needscomplete=True).supersubs(),inherited=[k.name for k in carry.subs.subs.subs],pos=self,verprot=1)
	@debugdebug
	def substitute(self,revf,repl):
		# if len(revf.data) == 0 and len(repl) == 0: return self
		return ObjKindUnionSet(subs=self.subs.substitute(revf,repl),inherited=self.inherited,pos=self,verprot=self.verprot)
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
		if type(subs) is DualSubs:
			# assert variables == None#safemode
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
		errors.takeblame(self)
		if self.verified: return self
		return ObjKindTypeUnion(subs=self.subs.verify(scope,errors),pos=self,exverified=True)
	@debugdebug
	def compactify(self,scope,subs,errors):
		return ObjKindTypeUnion(subs=self.subs.compactify(scope,subs,errors),pos=self,exverified=True)
	@debugdebug
	def substitute(self,revf,subs):
		# if len(revf.data) == 0 and len(subs) == 0: return self
		return ObjKindTypeUnion(subs=self.subs.substitute(revf,subs),pos=self,exverified=self.verified)
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry,errors):
		oafdjosidfjoasidf


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
		self.args = StratSeries() if args == None else StratSeries(args) if isinstance(args,list) else args
		self.name = name
		self.type = ty
		# assert self.name == None or type(self.name) is str or type(self.name) is list#safemode
		transferlines(self,pos)
		# assert issubclass(type(self.type),ObjKind)#safemode
		# assert type(self.args) is StratSeries#safemode
		self.verified = exverified and self.type.verified and self.args.verified
	def __repr__(self):
		if len(self.args.data) != 0:
			if self.name != None: return "["+",".join([str(k) for k in self.args.data])+"]"+str(self.name)+":"+str(self.type)
			else: return "["+",".join([str(k) for k in self.args.data])+"]"+str(self.type)
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
	def verify(self,scope,errors):
		global oneoff
		sarg = oneoff
		oneoff = False

		errors.takeblame(self)
		if self.verified: return self

		if sarg:print("I MEAN ALRIGHT")
		if sarg:prestart = time.time()
		verargs = self.args.verify(scope,errors)
		if sarg:start = time.time()

		# sresressres = None
		# if not sarg:
		sresressres = ObjStrategy(
			args=verargs,
			ty=self.type.verify(scope+verargs,ObjKindReferenceTree(name="U",verprot=2),errors),
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
		null,mmn = revf.integrate(self.args.introducer())
		return ObjStrategy(args=self.args.substitute(revf,repl),ty=self.type.substitute(mmn,repl),name=self.name,pos=self,exverified=self.verified)
	def refs(self,label):
		if self.args.refs(label): return True
		return not self.args.introducer().contains(label) and self.type.refs(label)
	def surfacerename(self,newname):
		if newname == self.name: return self
		# assert newname == None or type(newname) is str#safemode
		y = copy.copy(self)
		y.name = newname
		return y
	

	@debugdebug
	def split(self,semscope,errors):
		if type(self.name) is str: return [self]
		uoiu = self.ultimrename(semscope,SubsObject(),StratSeries(),self.name,[],errors,flat=True)

		return uoiu


	@debugdebug
	def bgroup(self,semscope,exsubs,prescope,mog,trail,errors):
		# assert self.verified#safemode
		# assert mog != None#safemode
		# assert self.name != None#safemode

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
			# assert k.verified#safemode
			po=[]
			for i in range(len(k.args.data)):
				nname = (str(depth)+":"+str(i-sera)) if i>=sera else k.args.data[i].name
				jjak = (depth+1) if i>=sera else minjcontains(k.args.data[i].name)

				ja = arbirow(jjak,len(k.args.data[i].args.data))
				jalarg = ObjKindReferenceTree(name=nname,args=simconvert(k.args.data[i],jjak),verprot=2)
				# assert jalarg.verified#safemode
				po.append(IndividualSub(k.args.data[i].name,ja,jalarg,[],k.args.data[i],exverified=True))
				# assert po[-1].verified#safemode
			return SubsObject(po,exverified=True)

		errors.takeblame(self)

		motype = self.type.substitute(RenamerObject(semscope+[k.name for k in prescope.flat]),exsubs)
		moargs = prescope+self.args.substitute(RenamerObject(semscope+[k.name for k in prescope.flat]),exsubs)
		mostrat = ObjStrategy(name=mog,ty=motype,args=moargs,exverified=True)
		nsfar = minjcontains(mog)

		if type(mog) is str:

			moh = ObjKindReferenceTree(name=mog,args=simconvert(mostrat,nsfar,sera=len(prescope.data)),verprot=2)#scrutinize sera
			if trail != None:
				for s in trail: moh = ObjKindReferenceTree(src=moh,name=s,verprot=0)
			return IndividualSub(None,arbirow(nsfar,len(self.args.data)),moh,[],mostrat,exverified=True)

		if type(self.type) is not ObjKindTypeUnion:
			raise errors.error("Mechanical error (subside): Non-unionset unwrapped in given paramter for eval. mog:"+str(mog)+" ,self: "+str(self))
		body = self.type.subs.availvariables()
		if len(mog) != len(body):
			raise errors.error("Mechanical error (subside): Wrong number of arguments for unwrap.")
		# assert trail == []#safemode


		jan = []
		voexsubs = exsubs
		erscope = semscope
		for i in range(len(body)):
			jan.append(body[i].bgroup(erscope,voexsubs,prescope,mog[i],[],errors))
			shim = body[i].ultimrename(erscope,voexsubs,prescope+self.args,mog[i],[],errors)

			erscope = erscope + ScopeIntroducer(body[i].name).allvars()
			voexsubs = voexsubs + shim[1]

		return IndividualSub(None,arbirow(nsfar,len(self.args.data)),ObjKindUnionSet(subs=jan,verprot=1),[],mostrat,exverified=True)
		#if this is supposedly verified then you need to have names for all the individualsubs that come back form bgroup.
		#	said names also need to match up with original.


	# def render(self,)



	@debugdebug
	def ultimrename(self,semscope,exsubs,prescope,mog,trail,errors,flat=False):
		# assert self.verified#safemode
		if type(mog) is ScopeIntroducer: mog = mog.dat
		# assert mog != None#safemode
		# assert self.name != None#safemode

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
			# assert k.verified#safemode
			po=[]
			for i in range(len(k.args.data)):
				nname = (str(depth)+":"+str(i-sera)) if i>=sera else k.args.data[i].name
				jjak = (depth+1) if i>=sera else minjcontains(k.args.data[i].name)

				ja = arbirow(jjak,len(k.args.data[i].args.data))
				jalarg = ObjKindReferenceTree(name=nname,args=simconvert(k.args.data[i],jjak),verprot=2)
				# assert jalarg.verified#safemode
				po.append(IndividualSub(k.args.data[i].name,ja,jalarg,[],k.args.data[i],exverified=True))
				# assert po[-1].verified#safemode
			return SubsObject(po,exverified=True)


		comscope = []

		errors.takeblame(self)
		if type(mog) is str:
			motype = self.type.substitute(RenamerObject(semscope+[k.name for k in prescope.flat]),exsubs)
			moargs = self.args.substitute(RenamerObject(semscope+[k.name for k in prescope.flat]),exsubs)

			mostrat = ObjStrategy(name=mog,ty=motype,args=prescope+moargs,exverified=True)

			if flat: return [mostrat]

			if len(trail) == 0: comscope.append(mostrat)

			if type(self.name) is str:
				llmostrat = ObjStrategy(name=mog,ty=motype,args=moargs,exverified=True)
				nsfar = minjcontains(mog)
				moh = ObjKindReferenceTree(name=mog,args=simconvert(mostrat,nsfar,sera=len(prescope.data)),verprot=2)#scrutinize sera

				for s in trail: moh = ObjKindReferenceTree(src=moh,name=s,verprot=0)

				mosub = IndividualSub(self.name,arbirow(nsfar,len(self.args.data)),moh,[],llmostrat,exverified=True)

			return (comscope,SubsObject([mosub]))
				
		if type(self.type) is not ObjKindTypeUnion:
			raise errors.error("Mechanical error (subside): Non-unionset unwrapped in given paramter for eval. mog:"+str(mog)+" ,self: "+str(self))
		body = self.type.subs.availvariables()
		if type(mog) is not str and len(mog) != len(body):
			raise errors.error("Mechanical error (subside): Wrong number of arguments for unwrap.")

		voexsubs = exsubs
		comsubs = SubsObject()
		erscope = semscope
		for i in range(len(body)):
			ntrail = trail+[(i,len(body))] if type(mog) is str else trail
			nmog = mog if type(mog) is str else mog[i]
			shim = body[i].ultimrename(erscope,voexsubs,prescope+self.args,nmog,ntrail,errors)
			erscope = erscope + ScopeIntroducer(body[i].name).allvars()
			comscope = comscope + shim[0]
			voexsubs = voexsubs + shim[1]
			comsubs = comsubs + shim[1]
		if flat: return comscope

		# for j in comscope:#safemode
			# assert j.verified#safemode


		zalo = comsubs.unitreformat(semscope,self,[k.name for k in body],self.name,errors,bonargs=self.args)


		return (comscope,zalo)





	@debugdebug
	def reformat(self,scope,mog,errors):
		# assert self.verified#safemode
		if type(mog) is ScopeIntroducer: mog = mog.dat

		errors.takeblame(self)
		if len(mog) != len(self.args.data):
			raise errors.error("Mechanical error (subside): Highly illegal compactify call.")
		if len(mog) == 0: return self

		body = self.args.flat
		if len(mog) != len(body):
			raise errors.error("Mechanical error (subside): Wrong number of arguments for unwrap.")

		comscope = []
		voexsubs = SubsObject()
		erscope = [k.name for k in scope.flat]
		for i in range(len(body)):
			shim = body[i].ultimrename(erscope,voexsubs,StratSeries(),mog[i],[],errors)
			erscope = erscope + ScopeIntroducer(body[i].name).allvars()
			comscope = comscope + shim[0]
			voexsubs = voexsubs + shim[1]

		sja = self.type.substitute(RenamerObject(erscope),voexsubs)
		goreturn = ObjStrategy(name=self.name,ty=sja,args=comscope).verify(scope,errors)
		# assert goreturn.verified#safemode
		return goreturn


	def equate(self,cno,other):
		if not self.args.equate(cno,other.args): return False
		return self.type.equate(other.sertequiv(self.introducer(),other.introducer()),other.type)



#architecture:
#natural rate context awareness?
#appraisal and generation could be alive too




#	code form
#review comments,prints,and assertions, and try/catches, and raises, and returns
#	take this serieously- more of the todo list is floating in the doc
#duplicate code in bgroup and reformat
#duplicate code in subs.reformat
#check all returns and args to see if its the wrapping class or just the internal, and establish some kind of convention



#	verification
#do a statement verify after



#   possible features
#implicit cast may also allow extra data (as in variables) to be stripped away.
#make strategy arguments into a dualsubs object
#make S satisfy {S} both positionally and when named; you can still have single-sub tuples...
#add ->()



#   possible bugs
#double check that ultimrename doesn't take you from a no scope occlusion situation to a scope occlusion situation.
#stratseries refs doesn't occlude any scope- is this normal?
#you do this pattern where you concatenate to subs... just make sure you dont get a pass by reference problem.
#expected doesn't really work with bon. review every usage
#individualsub substitute needs to handle expected, but it doesn't censor bon variables...
#what if you're renaming a strategy to an SI that the strategy accidently references?
#stratseries may need exverified back../.
#substitution on stratseries can leave it with a flat representation but not be verified...






