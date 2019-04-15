
from .structures import *



class ObjKind:pass


def mapping(subsf,subso,errors):
	construct = [None for n in subso]
	sht1 = 0
	sht2 = 0
	k=0
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
					k+=1
					break
			if not found:
				while sht2<len(subso) and subso[sht2].name != None:
					construct[sht2] = aj
					sht2 += 1
					found = True
					k+=1
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









def subsmake(lvluprow,mog,errors):
	if len(lvluprow) != len(mog):
		return errors.error("Wrong number of introduced parameters.")
	resk = []
	for f in range(len(lvluprow)):
		if isinstance(lvluprow[f],list):
			if len(mog[f].si) != 0:
				return errors.error("Mechanical error: Function-to-tuple unwrapping is not supported.")
			if type(mog[f].obj) is not ObjKindUnionSet:
				return errors.error("Mechanical error: non-unionset unwrapped in given paramter for eval.")
			resk = resk + subsmake(lvluprow[f],mog[f].obj.subs,errors)
		else:
			resk.append(IndividualSub(lvluprow[f],mog[f].si,mog[f].obj))
	return resk


def mostmeagername(exrevf,intrs,repl):
	assert type(exrevf) is RenamerObject
	assert type(repl) is SubsObject
	assert type(intrs) is ScopeIntroducer
	repls = {}
	for intr in intrs.allvars():
		if intr == None: continue
		if not repl.refs(intr): continue
		assert intr != "P"
		g = intr.split("$")
		assert len(g) == 1 or len(g) == 2
		n = int(g[0]) if len(g) == 2 else 1
		h = g[1] if len(g) == 2 else g[0]
		while repl.refs(str(n)+"$"+h) or str(n)+"$"+h in [a[1] for a in repls]:n+=1
		repls[intr] = str(n)+"$"+h
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

	def contains(self,label):
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
	def __init__(self,name,si,obj):
		assert type(name) is str or name == None
		assert type(si) is ScopeIntroducer
		assert issubclass(type(obj),ObjKind)
		self.name = name
		self.si = si
		self.obj = obj
	def __repr__(self):
		if self.name == None:
			return str(self.si)+str(self.obj)
		else:
			return self.name+"="+str(self.si)+str(self.obj)
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		mmn = mostmeagername(revf,self.si,repl)
		uhf = self.obj.substitute(mmn,repl.without(self.si),errors)
		if uhf == None: return
		return IndividualSub(self.name,self.si.rename(mmn),uhf)
	def refs(self,label:str):
		if self.si.contains(label): return False
		return self.obj.refs(label)

class SubsObject:
	def __init__(self,data):
		for k in data: assert type(k) is IndividualSub
		self.subs = data
	def __repr__(self):
		return ",".join([str(k) for k in self.subs])
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		nrepl = []
		for i in self.subs:
			marm = i.substitute(revf,repl,errors)
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
			if not i.si.contains(label) and i.obj.refs(label): return True
		return False
	def get(self,label:str):
		for t in reversed(self.subs):
			if t.name == label:
				return t
		return None
	def precompact(self,scope,cars,errors,onlycomplete=False,fumsub=False):
		assert type(scope) is StratSeries
		assert type(cars) is StratSeries
		assert type(errors) is ErrorObject
		# for j in sis: assert type(j) is ScopeIntroducer
		gar = mapping(self.subs,cars,errors)
		if gar == None: return

		simpsubs = []
		for z in range(len(gar)):
			if gar[z] == None:
				if not onlycomplete: continue
				if cars[z].name == None: return errors.error("Not enough positional arguments.")
				else: return errors.error("Missing named argument:"+cars[z].name)

			simpsubs.append(IndividualSub(cars[z].name,self.subs[gar[z]].si,self.subs[gar[z]].obj))



		srar = []
		rywe = cars.compactify(SubsObject(simpsubs),errors)
		if rywe == None: return
		valid = True
		for z in range(len(gar)):
			if gar[z] == None: continue

			shama = []
			for h in range(z):
				if gar[h] == None:
					if self.subs[gar[z]].refs(rywe[h].name) or rywe.data[z].refs(rywe[h].name):
						shama.append(rywe[h])


			zaku = rywe.data[z].compactify(self.subs[gar[z]].si,errors)
			if zaku == None:
				valid = False
				continue

			shse = self.subs[gar[z]].obj
			if fumsub:
				shse = shse.substitute(RenamerObject(),self.only(ScopeIntroducer([cars[y].name for y in range(z)])),errors)
				if shse == None:
					valid = False
					return
			shse = shse.verify(scope+StratSeries(shama)+zaku.args,zaku.type,errors)
			if shse == None:
				valid = False
				continue

			srar.append(IndividualOutSub(shse, self.subs[gar[z]].si ,rywe[z],StratSeries(shama)))
		return VerifiedSubs(StratSeries([rywe[h] for h in range(len(gar)) if gar[h] == None]),srar)
	def verify(self,scope,carry,errors:ErrorObject):
		if carry == None: return errors.error("Unable to deduce type of tuple.")
		assert type(carry) is ObjKind
		if type(carry) is not ObjKindTypeUnion: return errors.error("Can't pair keyword arguments to static type.")
		assert type(carry.subs) is VerifiedSubs

		return precompact(carry.variables,errors,True)
	def __len__(self):
		return len(self.subs)
		pass
class StratSeries:
	def __init__(self,data):
		for k in data: assert type(k) is ObjStrategy
		self.data = data
	def __repr__(self):
		return ",".join([str(i) for i in self.data])
	def verify(self,scope,errors:ErrorObject):
		zn = []
		for k in range(len(self.data)):
			zk = self.data[k].verify(scope+StratSeries(zn),errors)
			if zk == None: return
			zn.append(zk)
		return StratSeries(zn)
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		zn = []
		mmn = mostmeagername(revf,self.introducer(),repl)
		for k in range(len(self.data)):
			zk = self.data[k].substitute(mmn,repl.without(ScopeIntroducer([k.name for k in self.data[:k]])),errors)
			if zk == None: return
			zk.name = mmn[zk.name]
			zn.append(zk)
		return StratSeries(zn)
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

class IndividualOutSub:
	def __init__(self,obj,si,expected,zref):
		assert issubclass(type(obj),ObjKind)
		assert type(si) is ScopeIntroducer
		assert type(zref) is StratSeries
		self.obj = obj
		self.expected = expected
		self.zref = zref
		self.si = si
	def __repr__(self):
		return str(self.expected)+"="+str(self.si)+str(self.obj)
	def verify(self,scope:StratSeries,errors:ErrorObject):
		cs = self.zref.verify(scope,errors)
		ex = self.expected.verify(repl+self.zref,errors)
		marm = self.obj.verify(repl+self.zref+self.ex.args,errors)
		if cs == None or ex == None or marm == None: return
		return IndividualSub(marm,ex,cs)
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		mmn = mostmeagername(revf,self.zref.introducer(),repl)
		mmn2 = mostmeagername(mmn,self.si,repl)

		cs = self.zref.substitute(revf,repl,errors)
		ex = self.expected.substitute(mmn,repl.without(self.zref.introducer()),errors)
		ex.name = mmn[ex.name]
		marm = self.obj.substitute(mmn2,repl.without(self.zref.introducer()).without(self.si),errors)
		if cs == None or ex == None or marm == None: return
		return IndividualOutSub(marm,self.si.rename(mmn2),ex,cs)
	def compactify(self,subs,errors):
		cs = self.zref.compactify(repl,errors)
		shama = []
		for z in cs.data:
			for r in subs:
				if r.name == z.name:
					break
			else:
				shama.append(z)
		for r in subs:
			for z in cs.data:
				if r.name == z.name:
					break
			else:
				assert False

		ex = self.expected.substitute(RenamerObject(),repl,errors)
		marm = self.obj.substitute(RenamerObject(),repl.without(self.si),errors)
		if cs == None or ex == None or marm == None: return
		return IndividualSub(marm,ex,StratSeries(shama))
	def refs(self,label:str):
		if self.zref.refs(label): return True
		if self.zref.introducer().contains(label): return False
		if self.cs.refs(label): return True
		if self.cs.introducer().contains(label): return False
		if self.marm.refs(label): return True
		return False

class VerifiedSubs:
	def __init__(self,variables,out=None):
		if out == None: out = []
		for k in out: assert type(k) is IndividualOutSub
		assert type(variables) is StratSeries
		self.variables = variables
		self.outsubs = out
	def __repr__(self):
		if len(self.variables):
			if len(self.outsubs):
				return str(self.variables)+","+",".join([str(k) for k in self.subs])
			return str(self.variables)
		return ",".join([str(k) for k in self.subs])
	def verify(self,scope:StratSeries,errors:ErrorObject):
		nvars = self.variables.verify(scope,errors)
		suc = []
		for i in self.outsubs:
			swn = i.verify(scope,errors)
			if swn == None: return
			suc.append(swn)
		if nvars == None: return
		return VerifiedSubs(nvars,suc)
	def compactify(self,scope:StratSeries,subs:SubsObject,errors:ErrorObject):
		zon = subs.precompact(scope,self.variables,errors)
		if zon == None: return
		nout = []
		for i in self.outsubs:
			marm = i.compactify(zon.downcast(),errors)
			if marm == None:return
			nout.append(marm)
		return VerifiedSubs(zon.variables,nout+zon.outsubs)
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		nout = []
		dfhd = self.variables.substitute(revf,repl,errors)
		for i in self.outsubs:
			marm = i.substitute(revf,repl,errors)
			if marm == None:return
			nout.append(marm)
		return VerifiedSubs(dfhd,nout)
	def refs(self,label:str):
		for k in self.variables:
			if k.refs(label): return True
		for k in self.outsubs:
			if k.refs(label): return True
		return False
	def get(self,name:str,args:SubsObject,errors:ErrorObject):
		if args != None: assert type(args) is VerifiedSubs
		res = None
		for g in range(len(self.outsubs)):
			if self.outsubs[g].expected.name == name:
				res = self.outsubs[g]
		if res == None:
			return errors.error("No such property exists or the property exists but was not defined.")
		return res
	def downcast(self):
		assert len(self.variables) == 0
		return SubsObject([afd.append(IndividualSub(y.expected.name,y.expected.introducer(),y.obj)) for y in self.outsubs])






class ObjKindTemplateHolder(ObjKind):
	def __init__(self,src,subs):
		assert issubclass(type(src),ObjKind) and type(subs) is SubsObject
		self.src = src
		self.subs = subs
	def __repr__(self):
		return str(self.src)+"<"+str(self.subs)+">"
	def verify(self,scope,carry,errors):
		if self.subs == []: return src

		yu = self.src.verify(scope,None,errors)
		if yu == None: return
		if type(yu) is ObjKindReferenceTree:
			return ObjKindTemplateHolder(yu,self.subs)

		if type(yu) is ObjKindTypeUnion:
			return yu.compactify(scope,self.subs,errors)

		return errors.error("Substitution is only supported on unions.")#substitution is unsupported
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		tue = self.src.substitute(revf,repl,errors)
		ghy = self.subs.substitute(revf,repl,errors)
		if tue == None or ghy == None: return
		return ObjKindTemplateHolder(tue,ghy)

	def refs(self,label):
		return self.src.refs(label) or self.subs.refs(label)




class ObjKindReferenceTree(ObjKind):
	def __init__(self,lvlup=None,args=None,subs=None,src=None,parsed=None,upcast=None,name=None,pos=None):
		if args == None:
			self.args = SubsObject([])
			assert lvlup == None
		elif type(args) is SubsObject or type(args) is VerifiedSubs:
			self.args = args
			assert lvlup == None
		else:
			ijuh = []
			if lvlup == None:
				for z in args:
					ijuh.append(IndividualSub(None,ScopeIntroducer([]),z))
			else:
				assert len(lvlup) == len(args)
				for z in range(len(args)):
					ijuh.append(IndividualSub(None,ScopeIntroducer(lvlup[z]),args[z]))
			self.args = SubsObject(ijuh)

		if subs != None: assert type(subs) is SubsObject
		if src != None: assert issubclass(type(src),ObjKind)
		if name != None: assert type(name) is str
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

			namedargs = []
			anonyargs = []
			for u in range(ff+1,len(parsed)):
				if hasattr(parsed[u],'data') and parsed[u].data == 'objargument':#objargumentnamed
					anonyargs.append(parsed[u])
				if hasattr(parsed[u],'data') and parsed[u].data == 'objargumentnamed':#objargumentnamed
					namedargs.append(parsed[u])
			self.args = SubsObject([IndividualSub(None,ScopeIntroducer(k.children[:-1]),k.children[-1]) for k in anonyargs])
			ij = []
			for n in namedargs:
				if len(n.children)==1:
					ij.append(IndividualSub(None,ScopeIntroducer([s for s in n.children[0].children[:-1]]),n.children[0].children[-1]))
				else:
					ij.append(IndividualSub(n.children[0],ScopeIntroducer([s for s in n.children[1].children[:-1]]),n.children[1].children[-1]))
			self.subs = SubsObject(ij)
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
				dfji.append(IndividualSub(None,ScopeIntroducer([] if z>=len(upcast.lvlup) else upcast.lvlup[z]),ObjKindReferenceTree(upcast=upcast.args[z])))
			self.args = SubsObject(dfji)
			self.forgiveLvlup = True
		assert type(self.args) is SubsObject or type(self.args) is VerifiedSubs
		assert type(self.subs) is SubsObject or type(self.subs) is VerifiedSubs
	def __repr__(self):
		lab = "~anon~"
		if self.name != None: lab = self.name
		if len(self.subs) != 0: lab = lab+"<"+str(self.subs)+">"
		if len(self.args) != 0: lab = lab+"("+str(self.args)+")"
		return lab

	def verify(self,scope:StratSeries,carry,errors:ErrorObject):
		errors.takeblame(self)
		if self.src != None:
			poc = self.src.verify(scope,None,errors)
			if poc == None: return
			if type(poc) is ObjKindReferenceTree:
				return ObjKindReferenceTree(src=poc,args=self.args,subs=self.subs,name=self.name)
			if len(self.subs) > 0:
				if type(poc) is not ObjKindTypeUnion:
					return errors.error("Templating is only supported on type unions.")
				poc = poc.compactify(self.subs,errors)
			blcarry = poc.subs.get(self.name,errors)
			if blcarry == None: return
			if len(blcarry.zref) > 0:
				assert type(poc) is ObjKindTypeUnion
				return errors.error("The property accessed here is dependantly typed and refers to a variable that is unspecified. (Property cannot be used in static context.)")
			t = blcarry.expected
			si = blcarry.si
			zo = blcarry.obj
		else:
			t = scope.get(self.name)
			if t == None:
				print([scope[n].name for n in range(len(scope))])
				return errors.error("Referenced variable not in scope:"+self.name)
			zo = None
		

		if len(self.args) != len(t.args): return errors.error("Wrong argument count.")

		fas = []
		for j in range(len(self.args)):
			mogol = self.args.subs[j]
			if len(self.args.subs[j].si) != len(t.args[j].args):
				if self.forgiveLvlup and len(self.args.subs[j].si) < len(t.args[j].args):
					mogol = ScopeIntroducer(self.args.subs[j].si.data+[None for n in range(len(t.args[j].args)-len(self.args.subs[j].si))])
				else:
					return errors.error("Wrong number of introduced parameters.")
			fas.append(mogol)

		snot = SubsObject(fas).precompact(scope,t.args,errors,True)
		if snot == None: return

		if zo != None:
			gh = SubsObject(subsmake(si,fas,errors))
			if gh == None: return
			return zo.substitute(RenamerObject(),snot.downcast(),errors)

		zar = ObjKindReferenceTree(args=snot,subs=self.subs,name=self.name)
		zar.column = self.column
		zar.row = self.row
		return zar
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject

		moku = self.subs.substitute(revf,repl,errors)
		yobi = self.args.substitute(revf,repl,errors)
		uhji = None
		if self.src != None:
			uhij = self.src.substitute(revf,repl,errors)
			if uhji == None: return
			# if type(uhji) is not ObjKindReferenceTree:

			# 	what the fuck do i do here'

		if moku == None or yobi == None: return

		i = repl.get(self.name)
		if i == None:
			carry = ObjKindReferenceTree(args=yobi,src=uhji,name=revf[self.name],subs=moku)
			carry.column = self.column
			carry.row = self.row
			return carry

		gh = SubsObject(subsmake(i.si,yobi,errors))
		if gh == None: return
		uo = i.obj.substitute(revf.alternate(),gh,errors)
		if uo == None: return
		if moku == []: return uo
		return ObjKindTemplateHolder(src=uo,subs=moku)




	def render(self,scope,carry,errors):
		if self.src != None: return self.src.get(self.name,errors,self).render(scope,carry,errors)
		#referencing something? had better not be- substitute should scrub the whole damn mess clean.
		#no wait- there are variables.


	def refs(self,label):
		if self.name == label: return True
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
			for n in parsed:
				fjfj = []
				if len(n.children)==1:
					fjfj.append(IndividualSub(None,ScopeIntroducer([s for s in n.children[0].children[:-1]]),n.children[0].children[-1]))
				else:
					fjfj.append(IndividualSub(n.children[0],ScopeIntroducer([s for s in n.children[1].children[:-1]]),n.children[1].children[-1]))
				self.subs = SubsObject(fjfj)
	def __repr__(self):
		return "("+str(self.subs)+")"
		pass
	def verify(self,scope:StratSeries,carry,errors:ErrorObject):
		errors.takeblame(self)
		jdf = self.subs.verify(scope,carry,errors)
		if jdf == None: return
		zar = ObjKindUnionSet(subs=jdf)
		zar.column = self.column
		zar.row = self.row
		return zar
	def substitute(self,revf,repl,errors):
		assert type(revf) is RenamerObject and type(repl) is SubsObject and type(errors) is ErrorObject
		jdf = self.subs.substitute(revf,repl,errors)
		if jdf == None: return
		zar = ObjKindUnionSet(subs=jdf)
		zar.column = self.column
		zar.row = self.row
		return zar
	# def get(self,name:str,errors:ErrorObject):
	# 	return self.subs.get(name,errors)
	# 	pass
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry,errors):
		union


		#assemble UNION chain here...


class ObjKindTypeUnion(ObjKind):
	def __init__(self,parsed=None,variables=None,subs=None,pos=None):
		self.column = 0
		self.row = 0
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
		if parsed != None:
			assert variables == None
			assert subs == None
			self.variables = StratSeries([gh.children[0] for gh in parsed])
			argh = []
			for n in range(len(self.variables)):
				if len(parsed[n].children)==2:
					if self.variables[n].name != None:
						argh.append(IndividualSub(self.variables[n].name,ScopeIntroducer([j.name for j in self.variables[n].args]),parsed[n].children[1]))
			self.subs = SubsObject(argh)
		else:
			assert type(variables) is StratSeries
			self.variables = variables
			if subs == None:
				self.subs = SubsObject([])
			else:
				assert type(subs) is SubsObject or type(subs) is VerifiedSubs
				self.subs = subs
	def __repr__(self):
		if type(self.subs) is SubsObject:
			return "{"+str(self.variables)+"}"+"<"+str(self.subs)+">"
		return "{"+str(self.subs)+"}"
	def verify(self,scope:StratSeries,carry,errors:ErrorObject):
		errors.takeblame(self)
		print("---------->verifying:",self)


		assert type(self.subs) is SubsObject
		oufd = self.variables.verify(scope,errors)
		if oufd == None: return
		san = self.subs.precompact(scope,oufd,errors,fumsub=True)
		if san == None: return
		uad = ObjKindTypeUnion(variables=oufd,subs=san)
		uad.column = self.column
		uad.row = self.row
		return uad
	def compactify(self,scope:StratSeries,subs:SubsObject,errors:ErrorObject):
		assert type(self.subs) is VerifiedSubs
		idfj = self.variables.compactify(subs,errors)
		afud = self.subs.compactify(scope,subs,errors)
		if idfj == None or afud == None: return
		zar = ObjKindTypeUnion(variables = idfj,subs=afud)
		zar.column = self.column
		zar.row = self.row
		return zar
	def substitute(self,revf,subs,errors):
		assert type(revf) is RenamerObject and type(subs) is SubsObject and type(errors) is ErrorObject
		idfj = self.variables.substitute(revf,subs,errors)
		afud = self.subs.substitute(revf,subs,errors)
		if idfj == None or afud == None: return
		zar = ObjKindTypeUnion(variables = idfj,subs=afud)
		zar.column = self.column
		zar.row = self.row
		return zar
	# def get(self,name:str,errors:ErrorObject):
	# 	return self.subs.get(name,errors)
	# 	pass
	def refs(self,label:str):
		if self.variables.refs(label): return True
		if type(self.subs) is SubsObject and self.variables.introducer().contains(label): return False
		return self.subs.refs(label)



	def render(self,scope,carry,errors):
		assert self.subs == []

		#assemble AND chain here...




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
	def verify(self,scope:StratSeries,errors:ErrorObject):
		errors.takeblame(self)
		sna = self.args.verify(scope,errors)
		sja = self.type.verify(scope+self.args,ObjKindReferenceTree(name="U"),errors)
		if sna == None or sja == None: return
		mok = ObjStrategy(args=sna,ty=sja,name=self.name)
		mok.column = self.column
		mok.row = self.row
		return mok
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

	def compactify(self,mog:ScopeIntroducer,errors:ErrorObject):
		if len(mog) != len(self.args):
			return errors.error("Mechanical error (subside): Highly illegal compactify call.")

		def simconvert(k):
			return SubsObject([IndividualSub(None,i.introducer(),ObjKindReferenceTree(name=i.name,args=simconvert(i))) for i in k.args.data])

		def croconvert(j,k):
			if isinstance(j,list):
				if len(k.args) != 0:
					return errors.error("Mechanical error (subside): Function-to-tuple unwrapping is not supported.")
				if type(k.type) is not ObjKindUnionSet:
					return errors.error("Mechanical error (subside): non-unionset unwrapped in given paramter for eval.")
				if len(k.type.args) != len(j):
					return errors.error("Mechanical error (subside): Illegal unwrap length.")

				shar = [IndividualSub(None,k.type.args[i].introducer(),croconvert(j[i])) for i in range(len(j))]
				return ObjKindUnionSet(subs=SubsObject(shar))
			return ObjKindReferenceTree(name=j,args=simconvert(k))

		uio = []
		for g in range(len(mog)):
			moh = croconvert(mog.dat[g],self.args[g])
			if moh == None: return
			uio.append(IndividualSub(self.args[g].name,self.args[g].introducer(),moh))
		print("AJSKDL:JASKDL:")
		print("----compac->",[k.obj for k in uio])
		return self.substitute(RenamerObject(),SubsObject(uio),errors)


# substitute revf'


def metasyntaxreports(errors,window):
	errors = list(dict.fromkeys(errors.rer))
	phantoms = []
	scope = Scope([])
	for erroro in errors:
		error = '<span style="color:pink">█'+erroro[0]+'</span>'
		pos = window.view.text_point(erroro[1].row,erroro[1].column)
		phantoms.append(sublime.Phantom(
			sublime.Region(pos,pos+4),
			error,
			sublime.LAYOUT_BELOW
		))
	return phantoms















