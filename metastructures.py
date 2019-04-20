
from .structures import *



class ObjKind:pass



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
			if len(m.children) == 1 and type(m.children[0]) is str:pass
			moch = m.children[0 if len(m.children)==1 else 1]
			nname = m.children[0] if len(m.children)==2 else None

			nsi  = moch.children[:-1]
			nobj = moch.children[-1]
			nbon = [s.children[0] for s in parsed.children[:n] if type(s.children[0]) is str]
			ij.append(IndividualSub(nname,ScopeIntroducer(nsi),nobj,nbon))
		return SubsObject(ij)
	assert False










def debugdebug(F):
	def wrapper(*args,**kwargs):
		ahjs = F(*args,**kwargs)
		if ahjs == None:
			for k in args:
				if type(k) is ErrorObject:
					if len(k.rer) == 0:
						print("type:",type(args[0]))
						assert False
		return ahjs
	return wrapper



def mapping(subsf,subso,errors):
	construct = [None for n in subso]
	sht1 = 0
	sht2 = 0
	snarg = []
	for g in subsf:
		if g.name == None: continue
		if g.name in snarg: return errors.error("Duplicate keyword arguments are not allowed.")
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
				# while sht2<len(subso) and subso[sht2].name != None:
					if subso[ja].name != None:
						sht2 = ja+1
						construct[ja] = aj
						found = True
						break
			if not found:
				return errors.error("Too many positional arguments.")
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
						return errors.error("Parameter specified twice:" + subsf[aj].name)
				return errors.error("Unrecognized named parameter:" + subsf[aj].name)
	return construct


# def spushsubstitute(target,repl:SubsObject,errors:ErrorObject):
# 	uhf = target.substitute(tiu,repl.without(intrs),errors)
# 	if uhf == None: return None
# 	return (intrs.rename(tiu),uhf)

class RenamerObject:
	def __init__(self,data=None,alt=None):
		self.data = data if data != None else {}
		self.alt = alt if alt != None else {}
	def without(self,si):
		return RenamerObject({key:data for (key,data) in self.data.items() if not si.contains(key)},self.alt)
	def alternate(self):
		return RenamerObject(self.alt,self.data)
	def only(self,si):
		return RenamerObject({key:data for (key,data) in self.data.items() if si.contains(key)},self.alt)
	def __getitem__(self,key):
		return self.data.get(key,key)
	def __add__(self,other):
		df = self.data.copy()
		df.update(other.data)
		ud = self.alt.copy()
		ud.update(other.alt)
		return RenamerObject(df,ud)



class CrossNameObject:
	def __init__(self,data=None):
		self.data = [] if data == None else data
		pass
	def sertequiv(self,a,b):
		zar = a.paired(b)
		if zar == None: return
		return CrossNameObject(self.data+zar)
	def equivalen(self,a,b):
		for j in reversed(self.data):
			if j[0]==a or j[1] == b:
				return j[0] == a and j[1] == b
		return a==b




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


@debugdebug
def subsmake(lvluprow,mog,errors):
	if type(lvluprow) is ScopeIntroducer: lvluprow = lvluprow.dat
	assert type(errors) is ErrorObject and isinstance(lvluprow,list)
	if len(lvluprow) != len(mog):
		return errors.error("mechanical: Wrong number of introduced parameters.")
	resk = []
	for f in range(len(lvluprow)):
		if isinstance(lvluprow[f],list):
			if len(mog.subs[f].si) != 0:
				return errors.error("Mechanical error: Function-to-tuple unwrapping is not supported.")
			if type(mog.subs[f].obj) is not ObjKindUnionSet:
				# use a .get'
				resk = resk + internalsubsmake(lvluprow[f],mog.subs[f],[])
				# resk.append(ObjKindReferenceTree(src=mog.subs[f].obj,name=))

				# print("----->",mog.subs[f].obj)
				# assert False
				# return errors.error("Mechanical error: non-unionset unwrapped in given paramter for eval.")
			else:
				uio = subsmake(lvluprow[f],mog.subs[f].obj.subs,errors)
				if uio == None: return
				resk = resk + uio
		else:
			resk.append(IndividualSub(lvluprow[f],mog.subs[f].si,mog.subs[f].obj,[]))
	return resk


def mostmeagername(exrevf,intrs,repl):
	assert type(exrevf) is RenamerObject
	assert type(intrs)  is ScopeIntroducer
	repls = {}
	for intr in intrs.allvars():
		if intr == None: continue
		assert type(intr) is str
		if not repl.refs(intr): continue
		# assert intr != "P"
		g = intr.split("$")
		assert len(g) == 1 or len(g) == 2
		n = int(g[1]) if len(g) == 2 else 1
		h = g[0]
		while repl.refs(h+"$"+str(n)) or h+"$"+str(n) in repls.values():n+=1
		repls[intr] = h+"$"+str(n)
	return exrevf.without(intrs)+RenamerObject(repls)




class ErrorObject:
	def __init__(self,rer):
		self.rer = rer
		self.blame = None
		self.origin = None
	def takeblame(self,obk):
		self.blame = obk
	def acceptblame(self,obk):
		if self.blame == None: self.blame = obk
	def setorigin(self,obk):
		self.origin = obk
	def error(self,err:str,obk=None):
		if obk != None:
			self.rer.append((err,obk))
			return None
		if self.blame == None:
			if obk == None:
				self.rer.append((err,self.origin))
			else:
				self.rer.append((err,obk))
		else:
			self.rer.append((err,self.blame))
		return None
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
		assert type(revf) is RenamerObject
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
		pass


class IndividualSub:
	def __init__(self,name,si,obj,bon):
		assert type(name) is str or name == None
		assert type(si) is ScopeIntroducer
		assert issubclass(type(obj),ObjKind)
		self.name = name
		self.si = si
		self.obj = obj
		self.bon = bon

	def __repr__(self):
		if self.name == None:
			return str(self.si)+str(self.obj)
		else:
			return self.name+"="+str(self.si)+str(self.obj)
	@debugdebug
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		mmn = mostmeagername(revf,self.si,repl)
		uhf = self.obj.substitute(mmn,repl.without(ScopeIntroducer(self.bon)).without(self.si),errors)
		if uhf == None: return
		return IndividualSub(self.name,self.si.rename(mmn),uhf,self.bon)
	@debugdebug
	def compactify(self,repl,errors):
		assert type(repl) is SubsObject and type(errors) is ErrorObject
		mmn = mostmeagername(RenamerObject(),self.si,repl)
		uhf = self.obj.substitute(mmn,repl.only(ScopeIntroducer(self.bon)).without(self.si),errors)
		if uhf == None: return
		return IndividualSub(self.name,self.si.rename(mmn),uhf,[k for k in self.bon if repl.get(k) == None])
	def refs(self,label:str):
		if label in self.bon: return False
		if self.si.contains(label): return False
		return self.obj.refs(label)
	def equate(self,cno,other):
		con = cno.sertequiv(self.si,other.si)
		if con == None: return False
		return self.obj.equate(con,other.obj)
class SubsObject:
	def __init__(self,data=None):
		if data != None:
			for k in data: assert type(k) is IndividualSub
		self.subs = [] if data == None else data
	def __repr__(self):
		return ",".join([str(k) for k in self.subs])
	@debugdebug
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		nrepl = []
		for i in self.subs:
			marm = i.substitute(revf,repl,errors)
			if marm == None:return
			nrepl.append(marm)
		return SubsObject(nrepl)
	@debugdebug
	def compactify(self,repl,errors):
		assert type(repl) is SubsObject and type(errors) is ErrorObject
		nrepl = []
		for i in self.subs:
			marm = i.compactify(repl,errors)
			if marm == None:return
			nrepl.append(marm)
		return SubsObject(nrepl)
	def without(self,so:ScopeIntroducer):
		return SubsObject([d for d in self.subs if not so.contains(d.name)])
		pass
	def only(self,so:ScopeIntroducer):
		return SubsObject([d for d in self.subs if so.contains(d.name)])
		pass
	def refs(self,label:str):
		for i in self.subs:
			if i.refs(label): return True
		return False
	def get(self,label):
		if type(label) is int:
			if label>len(self.subs): return None
			return self.subs[label]
		for t in reversed(self.subs):
			if t.name == label:
				return t
		return None
	def redirect(self,a,b):
		assert type(a) is ScopeIntroducer and type(b) is ScopeIntroducer
		nrepl = []
		pairs = a.paired(b)
		for i in self.subs:
			marm = copy.copy(i)
			valid = True
			for pair in pairs:
				if marm.name == pair[0]:
					marm.name = pair[1]
					break
				if marm.name == pair[1]:
					valid = False
			else:
				if not valid: continue
			nrepl.append(marm)
		return SubsObject(nrepl)


	@debugdebug
	def precompact(self,scope,cars,errors,onlycomplete=False,argmode=False):
		assert type(scope) is StratSeries
		assert type(cars) is StratSeries
		assert type(errors) is ErrorObject
		if argmode:
			if len(self.subs) != len(cars): return errors.error("Illegal argument count.")
			gar = range(len(self.subs))
		else:
			gar = mapping(self.subs,cars,errors)
		if gar == None: return

		simpsubs = []

		zn = []


		for z in range(len(gar)):

			print("------>",cars[z])
			zaku = cars[z].substitute(RenamerObject(),SubsObject(simpsubs),errors)
			if zaku == None: return
			zn.append(zaku)


			if gar[z] == None:
				if not onlycomplete: continue
				if cars[z].name == None: return errors.error("Not enough positional arguments.")
				else: return errors.error("Missing named argument:"+cars[z].name)


			for check in self.subs[gar[z]].bon:
				if check not in [cars[k].name for k in range(z)] and self.subs[gar[z]].obj.refs(check) and not self.subs[gar[z]].si.contains(check):
					errors.append("This variable usage violates well-ordering property: "+check)



			koso = self.subs[gar[z]].compactify(SubsObject(simpsubs),errors)
			if koso == None: return

			jambo = []

			shama = StratSeries([])
			for h in reversed(range(z)):
				if gar[h] == None:
					if zn[h].name in koso.bon and koso.obj.refs(zn[h].name) and not koso.si.contains(zn[h].name):
						shama.data.insert(0,zn[h])
						jambo.append(zn[h].name)
						continue

					shouldinsert = False
					for yui in shama:
						if yui.refs(zn[h].name):
							shouldinsert = True
							break

					if shouldinsert:
						mmn = mostmeagername(RenamerObject(),ScopeIntroducer([zn[h].name]),shama)
						shama = shama.substitute(mmn,SubsObject([]),errors)
						zaku = zaku.substitute(mmn,SubsObject([]),errors)
						if shama == None or zaku == None: return
						zxc = copy.copy(zn[h])
						zxc.name = mmn[zxc.name]
						shama.data.insert(0,zxc)

			zakummn = mostmeagername(RenamerObject(),koso.si,zaku)
			nssi = koso.si.rename(zakummn)


			# uer = zaku
			zaku = zaku.substitute(zakummn,SubsObject(),errors)
			shse = koso.obj.substitute(zakummn,SubsObject(),errors)
			if zaku == None or shse == None: return

			# zakurenam = zaku
			# prezaku = zaku
			zaku = zaku.compactify(nssi,errors)
			if zaku == None: return

			# preshshe = shse
			shse = shse.verify(scope+shama+zaku.args,zaku.type,errors)
				# assert False
			if shse == None:
				# if len(zaku.args):
				# 	print("-=-=-=momo-=->",zaku.args.data)
				# 	print("-=-=-=blomo-=->",zakurenam.args.data)
				# 	print("-=-=-=anti-=->",uer.args.data)
				# 	print()
				# assert False
				return



			simpsubs.append(IndividualSub(cars[z].name,nssi,shse,jambo))


		return DualSubs(StratSeries(zn),SubsObject(simpsubs))
	@debugdebug
	def verify(self,scope,carry,errors:ErrorObject):
		if carry == None: return errors.error("Unable to deduce type of tuple.")
		assert issubclass(type(carry),ObjKind)
		if type(carry) is not ObjKindTypeUnion:
			assert False
			return errors.error("Can't pair keyword arguments to static type.")
		karo = self.precompact(scope,carry.subs.variables,errors,True)
		if karo == None: return
		return karo.subs
	def __len__(self):
		return len(self.subs)
		pass
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
	def __init__(self,data):
		for k in data: assert type(k) is ObjStrategy
		self.data = data
	def __repr__(self):
		return ",".join([str(i) for i in self.data])
	@debugdebug
	def verify(self,scope,errors:ErrorObject):
		zn = []
		for k in range(len(self.data)):
			zk = self.data[k].verify(scope+StratSeries(zn),errors)
			if zk == None:
				return
			zn.append(zk)
		return StratSeries(zn)
	@debugdebug
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		zn = []
		mmn = revf
		for k in range(len(self.data)):
			zk = self.data[k].substitute(mmn,repl.without(ScopeIntroducer([k.name for k in self.data[:k]])),errors)
			mmn = mostmeagername(mmn,ScopeIntroducer([self.data[k].name]),repl)
			if zk == None: return
			zk.name = mmn[zk.name]
			zn.append(zk)


		return StratSeries(zn)
	@debugdebug
	def compactify(self,repl:SubsObject,errors:ErrorObject):
		zn = []
		for k in range(len(self.data)):
			zk = self.data[k].substitute(RenamerObject(),repl.only(ScopeIntroducer([k.name for k in self.data[:k]])),errors)
			if zk == None: return
			zn.append(zk)
		return StratSeries(zn)
	def introducer(self):
		return ScopeIntroducer([k.name for k in self.data])
	def refs(self,label):
		if label != None: assert type(label) is str
		for k in self.data:
			if k.refs(label): return True
			if k.name == label: return False
		return False
	def get(self,label:str):
		for t in reversed(self.data):
			if t.name == label:
				return t
		return None
	def __add__(self,other):
		return StratSeries(self.data+other.data)
		pass
	def __len__(self):
		return len(self.data)
		pass
	def __getitem__(self, key):
		return self.data[key]
		pass
	def equate(self,cno,other):
		if len(self) != len(other): return False
		for i in range(len(self)):
			if not self[i].equate(cno,other[i]): return False
		return True



class DualSubs:
	def __init__(self,variables,subs=None):
		assert type(variables) is StratSeries
		if subs != None: assert type(subs) is SubsObject
		self.variables = variables
		self.subs = subs if subs != None else SubsObject([])
	def __repr__(self):
		dh = "{"+str(self.variables)+"}"
		if len(self.subs): dh = dh+"<"+str(self.subs)+">"
		return dh

	@debugdebug
	def verify(self,scope:StratSeries,errors:ErrorObject):
		nvars = self.variables.verify(scope,errors)
		if nvars == None: return
		return DualSubs(nvars).compactify(scope,self.subs,errors)

	@debugdebug
	def compactify(self,scope:StratSeries,subs:SubsObject,errors:ErrorObject):
		zon = subs.precompact(scope,self.variables,errors)
		sdj = self.subs.compactify(subs,errors)
		if zon == None or sdj == None: return
		return DualSubs(zon.variables,SubsObject(sdj.subs+zon.subs.subs))

	@debugdebug
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		dfhd = self.variables.substitute(revf,repl,errors)
		nout = self.subs.substitute(revf,repl,errors)
		if dfhd == None or nout == None: return
		return DualSubs(dfhd,nout)
	def refs(self,label:str):
		if self.variables.refs(label): return True
		if self.subs.refs(label): return True
		return False
	@debugdebug
	def get(self,name:str,errors:ErrorObject):
		return self.subs.get(name,errors)
	def equate(self,cno,other):
		#if type(other) is not DualSubs: return False
		return self.variables.equate(cno,other.variables) and self.subs.equate(cno,other.subs)





class ObjKindTemplateHolder(ObjKind):
	def __init__(self,src,subs):
		assert issubclass(type(src),ObjKind) and type(subs) is SubsObject
		self.src = src
		self.subs = subs
	def __repr__(self):
		return str(self.src)+"<"+str(self.subs)+">"
	@debugdebug
	def verify(self,scope,carry,errors):

		yu = self.src.verify(scope,None,errors)
		# jan = self.subs.precompact(scope,carry,errors)
		if yu == None: return
		if type(yu) is ObjKindReferenceTree:
			return ObjKindTemplateHolder(yu,self.subs)

		if type(yu) is ObjKindTypeUnion:
			return yu.compactify(scope,self.subs,errors)

		return errors.error("Substitution is only supported on unions.")#substitution is unsupported
	@debugdebug
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		tue = self.src.substitute(revf,repl,errors)
		ghy = self.subs.substitute(revf,repl,errors)
		if tue == None or ghy == None: return
		return ObjKindTemplateHolder(tue,ghy)
	def refs(self,label):
		return self.src.refs(label) or self.subs.refs(label)
	def equate(self,cno,other):
		assert False


class ObjKindReferenceTree(ObjKind):
	def __init__(self,lvlup=None,args=None,subs=None,src=None,parsed=None,upcast=None,name=None,pos=None):
		if args == None:
			self.args = SubsObject([])
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
		self.subs = subs if subs != None else SubsObject([])
		self.src = src
		self.column = 0
		self.row = 0
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
		if parsed != None:
			assert args == None
			assert subs == None
			assert src == None
			assert lvlup == None
			assert name == None
			assert upcast == None
			ff = 0
			if issubclass(type(parsed[0]),ObjKind):
				ff = 1
				self.src = parsed[0]
			self.name = parsed[ff]


			for u in parsed:
				if hasattr(u,'data') and u.data == 'objargumentseries':
					self.args = parsesubsfromsrc(u)
				if hasattr(u,'data') and u.data == 'objargumentnamedseries':
					self.subs = parsesubsfromsrc(u)
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
	def __repr__(self):
		lab = "~anon~"
		if self.name != None: lab = self.name
		if len(self.args) != 0: lab = lab+"("+str(self.args)+")"
		if len(self.subs) != 0: lab = lab+"<"+str(self.subs)+">"
		return lab

	@debugdebug
	def verify(self,scope:StratSeries,carry,errors:ErrorObject):

		errors.takeblame(self)
		# errors.error("O")
		if self.src != None:
			poc = self.src.verify(scope,None,errors)
			if poc == None: return
			if type(poc) is ObjKindReferenceTree:
				# errors.error("X")
				return ObjKindReferenceTree(src=poc,args=self.args,subs=self.subs,name=self.name)
			if len(self.subs) > 0:
				if type(poc) is not ObjKindTypeUnion:
					return errors.error("Templating is only supported on type unions.")
				poc = poc.compactify(self.subs,errors)
			blcarry = poc.subs.get(self.name,errors)
			if blcarry == None: 
				return errors.error("No such property exists or the property exists but was not defined.")
			if len(blcarry.zref) > 0:
				assert type(poc) is ObjKindTypeUnion
				return errors.error("The property accessed here is dependantly typed and refers to a variable that is unspecified. (Property cannot be used in static context.)")
			t = blcarry.expected
			assert False
			si = blcarry.si
			zo = blcarry.obj
		else:
			t = scope.get(self.name)
			if t == None:
				print([scope[n].name for n in range(len(scope))])
				return errors.error("Referenced variable not in scope:"+self.name)
			si = t.introducer()
			zo = None
		

		if len(self.args) != len(t.args): return errors.error("Wrong argument count.")

		fas = []
		for j in range(len(self.args)):
			mogol = self.args.subs[j]
			if len(self.args.subs[j].si) != len(t.args[j].args):
				if self.forgiveLvlup and len(self.args.subs[j].si) < len(t.args[j].args):
					mogol = ScopeIntroducer(self.args.subs[j].si.data+[None for n in range(len(t.args[j].args)-len(self.args.subs[j].si))])
				else:
					return errors.error("Wrong number of introduced parameters. expected "+str(len(t.args[j].args))+", got "+str(len(self.args.subs[j].si)),self.args.subs[j].obj)
			fas.append(mogol)

		snot = SubsObject(fas).precompact(scope,t.args,errors,onlycomplete=True,argmode=True)
		if snot == None: return
		snot = snot.subs

		if carry != None:
			exptyoe = t.type.substitute(RenamerObject(),snot,errors)
			if exptyoe == None: return

			def recurstep(exptyoe):
				valids = 0
				if exptyoe.equate(CrossNameObject(),carry):
					valids += 1
				elif type(exptyoe) is ObjKindTypeUnion:
					for j in exptyoe.subs.variables:
						if len(j.args) == 0:
							valids += recurstep(j.type)
				return valids

			valids = recurstep(exptyoe)

			if valids > 1:
				return errors.error("unable to infer which member to extract from composite type")
			if valids == 0:
				return errors.error(str(exptyoe)+" =/= "+str(carry))

		if zo != None:
			gh = subsmake(si,fas,errors)
			if gh == None: return
			return zo.substitute(RenamerObject(),SubsObject(gh),errors)

		zar = ObjKindReferenceTree(args=snot,subs=self.subs,name=self.name)
		zar.column = self.column
		zar.row = self.row
		return zar
	@debugdebug
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject

		moku = self.subs.substitute(revf,repl,errors)
		yobi = self.args.substitute(revf,repl,errors)
		if self.src != None:
			uhji = self.src.substitute(revf,repl,errors)
			if uhji == None: return

			carry = ObjKindReferenceTree(args=yobi,src=uhji,name=self.name,subs=moku)
			carry.column = self.column
			carry.row = self.row
			return carry
			# if type(uhji) is not ObjKindReferenceTree:

			# 	what the fuck do i do here'

		if moku == None or yobi == None: return

		i = repl.get(self.name)
		if i == None:
			carry = ObjKindReferenceTree(args=yobi,name=revf[self.name],subs=moku)
			carry.column = self.column
			carry.row = self.row
			return carry

		shmo = subsmake(i.si,yobi,errors)
		if shmo == None: return
		uo = i.obj.substitute(revf.alternate(),SubsObject(shmo),errors)
		if uo == None: return

		if len(moku) == 0: return uo
		return ObjKindTemplateHolder(src=uo,subs=moku)
	def render(self,scope,carry,errors):
		soijfasijef
		#referencing something? had better not be- substitute should scrub the whole damn mess clean.
		#no wait- there are variables.
	def equate(self,cno,other):
		if type(other) is not ObjKindReferenceTree: return False
		if not cno.equivalen(self.name,other.name): return False
		if self.src == None and other.src == None: return True
		if self.src == None or other.src == None: return False
		return self.args.equate(cno,other.args) and self.subs.equate(cno,other.subs)
	def refs(self,label):
		if self.src == None and self.name == label: return True
		if self.args.refs(label): return True
		if self.subs.refs(label): return True
		if self.src != None and self.src.refs(label): return True
		return False

class ObjKindUnionSet(ObjKind):
	def __init__(self,subs=None,parsed=None,pos=None):
		self.subs = SubsObject([]) if subs == None else subs
		self.column = 0
		self.row = 0
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
		if parsed != None:
			assert subs == None
			self.subs = parsesubsfromsrc(parsed[0])
	def __repr__(self):
		return "("+str(self.subs)+")"
		pass
	@debugdebug
	def verify(self,scope:StratSeries,carry,errors:ErrorObject):
		errors.takeblame(self)
		jdf = self.subs.verify(scope,carry,errors)
		if jdf == None: return
		zar = ObjKindUnionSet(subs=jdf)
		zar.column = self.column
		zar.row = self.row
		return zar
	@debugdebug
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		jdf = self.subs.substitute(revf,repl,errors)
		if jdf == None: return
		zar = ObjKindUnionSet(subs=jdf)
		zar.column = self.column
		zar.row = self.row
		return zar
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry,errors):
		union


		#assemble UNION chain here...
	def equate(self,cno,other):
		if type(other) is not ObjKindUnionSet: return False
		return self.subs.equate(cno,other.subs)

class ObjKindTypeUnion(ObjKind):
	def __init__(self,parsed=None,subs=None,variables=None,pos=None):

		self.column = 0
		self.row = 0
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
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
				subi = SubsObject([]) if subs == None else subs
				vari = StratSeries([]) if variables == None else variables if type(variables) is StratSeries else StratSeries(variables)
				print("-----=====>",vari,variables)
				self.subs = DualSubs(vari,subi)
	def __repr__(self):
		return str(self.subs)
	@debugdebug
	def verify(self,scope:StratSeries,carry,errors:ErrorObject):
		errors.takeblame(self)
		san = self.subs.verify(scope,errors)
		if san == None: return
		uad = ObjKindTypeUnion(subs=san)
		uad.column = self.column
		uad.row = self.row
		return uad
	@debugdebug
	def compactify(self,scope:StratSeries,subs:SubsObject,errors:ErrorObject):
		san = self.subs.compactify(scope,subs,errors)
		if san == None: return
		zar = ObjKindTypeUnion(subs=san)
		zar.column = self.column
		zar.row = self.row
		return zar
	@debugdebug
	def substitute(self,revf,subs,errors):
		assert type(revf) is RenamerObject and type(subs) is SubsObject and type(errors) is ErrorObject
		san = self.subs.substitute(revf,subs,errors)
		if san == None: return
		zar = ObjKindTypeUnion(subs=san)
		zar.column = self.column
		zar.row = self.row
		return zar
	def refs(self,label:str):
		return self.subs.refs(label)
	def render(self,scope,carry,errors):
		oafdjosidfjoasidf
		#assemble AND chain here...
	def equate(self,cno,other):
		if type(other) is not ObjKindTypeUnion: return False
		return self.subs.equate(cno,other.subs)


class ObjStrategy:
	def __init__(self,args=None,parsed=None,ty=None,name=None,upcast=None,pos=None):
		self.args = StratSeries([]) if args == None else StratSeries(args) if isinstance(args,list) else args
		self.name = name
		self.type = ty
		self.column = 0
		self.row = 0
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
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
		assert issubclass(type(self.type),ObjKind)
		assert type(self.args) is StratSeries
	def __repr__(self):
		if len(self.args) != 0:
			if self.name != None: return "["+",".join([str(k) for k in self.args])+"]"+self.name+":"+str(self.type)
			else: return "["+",".join([str(k) for k in self.args])+"]"+str(self.type)
		else:
			if self.name != None: return self.name+":"+str(self.type)
			else: return str(self.type)
	@debugdebug
	def verify(self,scope:StratSeries,errors:ErrorObject):
		errors.takeblame(self)
		sna = self.args.verify(scope,errors)
		sja = self.type.verify(scope+self.args,ObjKindReferenceTree(name="U"),errors)
		if sna == None or sja == None: return
		mok = ObjStrategy(args=sna,ty=sja,name=self.name)
		mok.column = self.column
		mok.row = self.row
		return mok
	@debugdebug
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		mmn = mostmeagername(revf,self.introducer(),repl)

		sna = self.args.substitute(revf,repl,errors)
		sja = self.type.substitute(mmn,repl.without(self.args.introducer()),errors)
		if sna == None or sja == None: return
		mok = ObjStrategy(args=sna,ty=sja,name=self.name)
		mok.column = self.column
		mok.row = self.row
		return mok
	def refs(self,label:str):
		if self.args.refs(label): return True
		return not self.args.introducer().contains(label) and self.type.refs(label)
	def introducer(self):
		return ScopeIntroducer([k.name for k in self.args])
		pass

	@debugdebug
	def compactify(self,mog:ScopeIntroducer,errors:ErrorObject):
		if len(mog) != len(self.args):
			return errors.error("Mechanical error (subside): Highly illegal compactify call.")

		def arbirow(depth,length):
			return ScopeIntroducer([str(depth)+":"+str(h) for h in range(length)])

		def simconvert(k,depth):
			po=[]
			for i in range(len(k.args)):
				ja = arbirow(depth+1,len(k.args[i].args))
				po.append(IndividualSub(None,ja,ObjKindReferenceTree(name=str(depth)+":"+str(i),args=simconvert(k.args[i],depth+1)),[]))
			return SubsObject(po)

		def croconvert(j,k):
			if isinstance(j,list):
				if len(k.args) != 0:
					return errors.error("Mechanical error (subside): Function-to-tuple unwrapping is not supported.")
				if type(k.type) is not ObjKindTypeUnion:
					return errors.error("Mechanical error (subside): non-unionset unwrapped in given paramter for eval. "+str(mog)+" , "+str(self))
				if len(k.type.subs.variables) != len(j):
					return errors.error("Mechanical error (subside): Illegal unwrap length.")

				shar = [IndividualSub(None,arbirow(0,len(k.type.subs.variables[i].args)),croconvert(j[i],k.type.subs.variables[i]),[]) for i in range(len(j))]
				return ObjKindUnionSet(subs=SubsObject(shar))
			return ObjKindReferenceTree(name=j,args=simconvert(k,0))

		def populate(j,k,repl):
			if isinstance(j,list):
				assert len(k.args) == 0
				assert type(k.type) is ObjKindTypeUnion
				assert len(k.type.subs.variables) == len(j)

				return [u for i in range(len(j)) for u in populate(j[i],k.type.subs.variables[i],repl)]

			mold = k.substitute(RenamerObject(),repl,errors)
			mold.name = j
			return [mold]


		nargs = []

		uio = []
		for g in range(len(mog)):
			nargs = nargs + populate(mog.dat[g],self.args[g],SubsObject(uio))
			moh = croconvert(mog.dat[g],self.args[g])
			if moh == None: return
			uio.append(IndividualSub(self.args[g].name,arbirow(0,len(self.args[g].args)),moh,[]))

		sja = self.type.substitute(RenamerObject(),SubsObject(uio),errors)


		# if len(uio) != 0: assert False
		return ObjStrategy(name=self.name,ty=sja,args=StratSeries(nargs))


	def equate(self,cno,other):
		if self.name != other.name: return False
		if not self.args.equate(cno,other.args): return False
		if not self.type.equate(cno,other.type): return False
		return True





# substitute revf'


def metasyntaxreports(errors,window):
	errors = list(dict.fromkeys([(o[0],o[1].row,o[1].column) for o in errors.rer]))
	phantoms = []
	scope = Scope([])
	for erroro in errors:
		error = '<span style="color:pink">█'+erroro[0].replace('>','&gt;').replace('<','&lt;')+'</span>'
		pos = window.view.text_point(erroro[1],erroro[2])
		phantoms.append(sublime.Phantom(
			sublime.Region(pos,pos+4),
			error,
			sublime.LAYOUT_BELOW
		))
	return phantoms










