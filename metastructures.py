

# import time
# from .debugging import debugdebug, ErrorObject


# fonocolls = 0
# fonodepth = 0


# class DescendObject:
# 	def __init__(self,remap,repl,scope):#empty constructor
# 		self.mmn
# 		self.subs
# 		self.scope



# 	def append(self,newscope):

# 	def substitute(self,revf,repl):

# 		match up scope and shizz.



# 		concat = {}
# 		for k,v in revf.data.items():
# 			concat[v] = k
# 		for k,v in self.precapture.items():
# 			concat[revf.data.get(k,k)] = v

# 		# 	is there really a need for precapture? you can just take the ending tags off.


# 		oust = [k for k in repl.subs if type(k) is not DowngradeSub]
# 		for jy in self.captured.substitute(revf,repl).subs:
# 			yj = copy.copy(jy)
# 			yj.name = revf.data.get(yj.name,yj.name)
# 			oust.append(yj)

# 		return DescendObject()
# 		#,precapture=concat
# 		return ObjKindWildcard(pos=self,captured=SubsObject(oust),exverified=self.verified,unobject=self.unobject)


# class RenamerObject:
# 	def __init__(self,scope,data=None):
# 		if type(scope) is StratSeries:
# 			self.s = [k.name for k in scope.flat]
# 		else:
# 			self.s = scope
# 		# for x in range(len(self.s)):#safemode
# 			# for y in range(x):#safemode
# 				# assert self.s[x]!=self.s[y]#safemode


# 		self.data = data if data != None else {}

# 	def integrate(self,si):
# 		def meager(forbidden,intr):
# 			if intr == None: intr = "%"
# 			if type(forbidden) is dict: forbidden = forbidden.values()
# 			if intr not in forbidden: return intr
# 			g = intr.split("$")
# 			# assert len(g) == 1 or len(g) == 2#safemode
# 			n = int(g[1]) if len(g) == 2 else 1
# 			h = g[0]
# 			while h+"$"+str(n) in forbidden: n+=1
# 			return h+"$"+str(n)


# 		repls = copy.copy(self.data)
# 		pres = []

# 		def croc(intr):
# 			if isinstance(intr,list):
# 				return [croc(i) for i in intr]
# 			z = meager(self.s+pres,intr)
# 			pres.append(z)
# 			if intr != z: repls[intr] = z
# 			return z
# 		return (ScopeIntroducer(croc(si.dat)),RenamerObject(self.s+pres,repls))



# 	def __repr__(self):
# 		return "|"+str(self.s)+"|"+",".join([a[0]+"-->"+a[1] for a in self.data.items()])

# 	def __getitem__(self,key):
# 		# print("searching",key)
# 		# if key != "U" and key not in self.s:#safemode
# 			# print("not found:",key)#safemode
# 			# assert False#safemode
# 			# ErrorObject.fatal("not found: "+key)#safemode
# 		return self.data.get(key,key)


# class CrossNameObject:
# 	def __init__(self,data=None):
# 		self.data = [] if data == None else data
# 	def sertequiv(self,a,b):
# 		zar = a.paired(b)
# 		if zar == None: return
# 		return CrossNameObject(self.data+zar)
# 	def flip(self):
# 		return CrossNameObject([(b,a) for a,b in self.data])
# 	def equivalen(self,a,b):
# 		for j in reversed(self.data):
# 			if j[0]==a or j[1] == b:
# 				return j[0] == a and j[1] == b
# 		return a==b


# def allvars(ju):
# 	if isinstance(ju,list):
# 		return [g for i in ju for g in allvars(i)]
# 	return [ju]
# class ScopeIntroducer:
# 	def __init__(self,dat):
# 		self.dat = dat
# 		# def shmo(o):#safemode
# 			# if isinstance(o,list):#safemode
# 				# for i in o: shmo(i)#safemode
# 			# else:#safemode
# 				# assert type(o) is str or o == None#safemode
# 		# shmo(dat)#safemode
# 	def __repr__(self):
# 		def pretty(j):
# 			if isinstance(j,list): return "("+",".join([pretty(i) for i in j])+")"
# 			return str(j)
# 		if len(self.dat) == 0: return ""
# 		return "["+",".join([pretty(i) for i in self.dat])+"]"
# 	def paired(self,other):
# 		def croc(a,b):
# 			if isinstance(a,list) and isinstance(b,list):
# 				if len(a) != len(b): return None
# 				fo = []
# 				for i in range(len(a)):
# 					ui = croc(a[i],b[i])
# 					if ui == None: return None
# 					fo = fo + ui
# 				return fo
# 			if isinstance(a,list) or isinstance(b,list): return None
# 			return [(a,b)]
# 		return croc(self.dat,other.dat)
# 	def contains(self,label):
# 		if label == None: return False
# 		# assert type(label) is str#safemode
# 		def contains(lvluprow):
# 			for h in lvluprow:
# 				if h == label: return True
# 				if isinstance(h,list) and contains(h): return True
# 			return False
# 		return contains(self.dat)

# 	def astring(self,exp):
# 		def inter(j,exp):
# 			if isinstance(j,list):
# 				if exp == None: return "("+",".join(["[...]"+inter(p,None) for p in j])+")"
# 				dunc = []
# 				for p in range(len(j)):
# 					dun = ""
# 					yada = exp[p].args.lenavail()
# 					if yada != 0: dun = "["+",".join(["_"]*yada)+"]"
# 					gtr = exp[p].type.subs.availvariables() if type(exp[p].type) is ObjKindTypeUnion else None
# 					dunc.append(dun+inter(j[p],gtr))
# 				return "("+",".join(dunc)+")"
# 			return "~"
# 		return inter(self.dat,exp.availvariables() if exp!=None else None)




# 	def allvars(self):
# 		return allvars(self.dat)
# 	def __len__(self):
# 		return len(self.dat)
# 	def __eq__(self,other):
# 		if type(other) is not ScopeIntroducer: return False
# 		return self.dat == other.dat
# class DownBonObject:
# 	def __init__(self,avail,si):
# 		self.avail = avail
# 		self.si = si
# 	def jsi(self):
# 		return ScopeIntroducer([self.si.dat[k] for k in range(len(self.avail)) if self.avail[k]])
# 	def jdb(self):
# 		return ScopeIntroducer([self.si.dat[k] if not self.avail[k] else None for k in range(len(self.avail))])


# #-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=


# # class PlaceholderSub(SubRow):
# # 	def __init__(self,label,si=None):
# # 		self.name = label
# # 		self.si = si
# # 		self.verified = True
# # 		# assert type(label) is str or label == None or type(label) is list#safemode
# # 		# assert si == None or type(si) is ScopeIntroducer#safemode
# # 	def __repr__(self):
# # 		return "@"+str(self.si)+str(self.name)
# # 	def wide_repr(self,depth):
# # 		return str(self)

# # 	def refs(self,label):
# # 		return False
# # 	@debugdebug
# # 	def equate(self,cno,other):
# 		return type(other) is PlaceholderSub
# 	# def substitute(self,a,b):
# 		return self


# review expected...
# its an object now, not a strategy.


# class Lambda:
# 	def __init__(self,si,obj):
# 		assert type(si) is ScopeIntroducer or type(si) is DualSubs
# 		self.si = si



# class TypeRow(SubRow):
# 	def __init__(self,type,obj=None):
# 		self.type = type
# 		self.obj  = obj



# class SubRow(SubRow):
# 	def __init__(self,name,obj,inherited=False):
# 		# assert type(name) is str or name == None or type(name) is list#safemode
# 		self.name = name
# 		self.obj  = obj
# 		self.inherited = inherited


# 	def 



# 	when you pass an actual function




# 	def __repr__(self):
# 		res = ""
# 		if self.name != None: res = res+str(self.name)+"="
# 		# if self.expected != None: res = res+"<<!"+str(self.expected)+"!>>"
# 		if self.bon != None: res = res+str(self.bon)+"|"
# 		res = res+str(self.si)+str(self.obj)
# 		return res
# 	def wide_repr(self,depth):
# 		res = ""
# 		if self.name != None: res = res+self.name+"="
# 		# if self.expected != None: res = res+"<<!"+str(self.expected)+"!>>"
# 		if self.bon != None: res = res+str(self.bon)+"|"
# 		res = res+str(self.si)+self.obj.wide_repr(depth)
# 		return res
# 	@debugdebug
# 	def substitute(self,revf,repl):
# 		mmn = revf
# 		nbon = None
# 		ndow = None

# 		if self.bon != None: nbon,mmn = mmn.integrate(self.bon)

# 		if self.downbon == None:
# 			nsi,mmn = mmn.integrate(self.si)
# 		else:
# 			fff,mmn = mmn.integrate(self.downbon.si)
# 			ndow = DownBonObject(self.downbon.avail,fff)
# 			nsi = ndow.jsi()

# 		uhf = self.obj.substitute(mmn,repl)

# 		jae = None if self.expected == None else self.expected.substitute(revf,repl)

# 		return IndividualSub(self.name,nsi,uhf,bon=nbon,exverified=self.verified,inherited=self.inherited,downbon=ndow,expected=jae)
# 	def refs(self,label):
# 		if self.si.contains(label): return False
# 		if self.bon.contains(label): return False
# 		if self.downbon != None and self.downbon.si.contains(label): return False
# 		return self.obj.refs(label)
# 	@debugdebug
# 	def equate(self,cno,other):
# 		if type(other) is PlaceholderSub: return False
# 		con = cno.sertequiv(self.si,other.si)
# 		if con == None: return False
# 		if self.bon != None and other.bon != None: con = con.sertequiv(self.bon,other.bon)
# 		if con == None: return False
# 		soul = self.obj.equate(con,other.obj)
# 		return soul
# 	@debugdebug
# 	def unwrapsubs(self,mog,prep=None,onlyavailable=False):
# 		if prep == None: prep = []
# 		prep = prep+self.si.dat
# 		# assert self.downbon == None and self.bon == None#safemode
# 		def internalsubsmake(mog,trail,prep):
# 			if isinstance(mog,list):
# 				i = []
# 				for f in range(len(mog)):
# 					i = i + internalsubsmake(mog[f],trail+[(f,len(mog))],prep)
# 				return i
# 			jog = self.obj
# 			for s in trail:
# 				jog = ObjKindReferenceTree(src=jog,name=s,verprot=0)
# 			return [IndividualSub(mog,ScopeIntroducer(prep),jog,exverified=True)]
# 		if isinstance(mog,list):
# 			if type(self.obj) is not ObjKindUnionSet:
# 				return internalsubsmake(mog,[],prep)
# 			else:
# 				return self.obj.subs.unwrapsubs(mog,prep=prep,onlyavailable=onlyavailable)
# 		else:
# 			return [IndividualSub(mog,ScopeIntroducer(prep),self.obj,exverified=True)]
# 	def seekstrat(self,mog,prep=None,onlyavailable=False):
# 		if prep == None: prep = DualSubs()
# 		prep = prep+self.expected.args
# 		# assert self.downbon == None and self.bon == None#safemode
# 		# assert self.expected.args.semavail().dat == self.si.dat#safemode
# 		if isinstance(mog,list):
# 			# assert type(self.obj) is ObjKindUnionSet#safemode
# 			return self.obj.subs.seekstrat(mog,prep=prep,onlyavailable=onlyavailable)
# 		else:
# 			return [ObjStrategy(args=prep,name=mog,ty=self.expected.type,exverified=True)]
# class DowngradeSub(SubRow):
# 	def __init__(self,cap,name):
# 		self.cap = cap
# 		self.name = name
# 		# assert type(name) is str#safemode
# 	def unwrapsubs(self,mog,prep=None,onlyavailable=None):
# 		# assert type(mog) is str#safemode
# 		return [DowngradeSub(self.cap,mog)]
# 	def __repr__(self):
# 		return "DOWNGRADE:"+self.name+str(len(self.cap))

# class SubsObject:
# 	def __init__(self,data=None,exverified=False,pos=None):
# 		# if data != None:#safemode
# 			# for k in data: assert issubclass(type(k),SubRow)#safemode

# 		self.subs = [] if data == None else data
# 		self.verified = (exverified and all(i.verified for i in self.subs)) or self.subs == []

# 		# for k in range(len(self.subs)):#safemode
# 			# if type(self.subs[k]) is not IndividualSub: continue#safemode
# 			# if self.subs[k].bon != None:#safemode
# 				# assert len(self.subs[k].bon.dat) == k#safemode

# 		transferlines(self,pos)


# 	def __repr__(self):
# 		return ",".join([str(k) for k in self.subs])
# 	def wide_repr(self,depth):
# 		sep = "\n"+"\t"*depth
# 		return sep+(","+sep).join([k.wide_repr(depth+1) for k in self.subs])
# 	def oblong_repr(self,depth):
# 		return ",".join([k.wide_repr(depth) for k in self.subs])
# 	@debugdebug
# 	def substitute(self,revf,repl):
# 		return SubsObject([i.substitute(revf,repl) for i in self.subs],exverified=self.verified,pos=self)
# 	def onlyreal(self):
# 		return SubsObject([k for k in self.subs if type(k) is IndividualSub and not k.inherited],pos=self)


# 	def triangulate(self,semscope):
# 		out = []
# 		for h in self.subs:
# 			if type(h) is PlaceholderSub:
# 				assert False
# 				out.append(None)
# 			elif h.bon == None: out.append(h)
# 			else:
# 				d = copy.copy(h)
# 				nbon,mmn = RenamerObject(semscope).integrate(d.bon)
# 				d.bon = None
# 				out.append(d.substitute(mmn,SubsObject(SubsObject([e for e in out if e != None]).unwrapsubs([nbon.dat[e] for e in range(len(nbon.dat)) if out[e] != None]),pos=self)))
# 		return SubsObject([e for e in out if e != None],pos=self)
# 	@debugdebug
# 	def unwrapsubs(self,mog,prep=None,onlyavailable=False):
# 		if type(mog) is ScopeIntroducer: mog = mog.dat
# 		# assert type(mog) is not str#safemode

# 		ju = [k for k in self.subs if not k.inherited] if onlyavailable else self.subs
# 		if len(mog) == len(ju): 
# 			rtse = []
# 			for f in range(len(ju)):
# 				rtse = rtse + ju[f].unwrapsubs(mog[f],prep=prep,onlyavailable=onlyavailable)
# 			return rtse
# 		elif len(ju) == 1:
# 			return ju[0].unwrapsubs(mog,prep=prep,onlyavailable=onlyavailable)
# 		elif len(mog) == 1 and type(mog[0]) is list:
# 			return self.unwrapsubs(mog[0],prep=prep,onlyavailable=onlyavailable)
# 		else:
# 			# assert False
# 			ErrorObject.fatal("Incorrect unwrap length...")
# 	def seekstrat(self,mog,prep=None,onlyavailable=False):
# 		if type(mog) is ScopeIntroducer: mog = mog.dat
# 		# assert type(mog) is not str#safemode
# 		ju = [k for k in self.subs if not k.inherited] if onlyavailable else self.subs
# 		# assert len(mog) == len(ju)#safemode
# 		rtse = []
# 		for f in range(len(ju)): rtse = rtse + ju[f].seekstrat(mog[f],prep=prep,onlyavailable=onlyavailable)
# 		return rtse
# 	def __add__(self,other):
# 		# assert type(other) is SubsObject#safemode
# 		return SubsObject(self.subs+other.subs,exverified=self.verified and other.verified)
# 	def refs(self,label):
# 		for i in self.subs:
# 			k = i.refs(label)
# 			if k: return k
# 		return False
# 	def get(self,label):
# 		if type(label) is tuple:
# 			if label[1]!=len([k for k in self.subs if not k.inherited]): ErrorObject.fatal("mechanical: Wrong number of introduced parameters.")
# 			return [k for k in self.subs if not k.inherited][label[0]]
# 		for t in reversed(self.unwrapsubs([k.name for k in self.subs])):
# 			if t.name == label:
# 				if type(t) is PlaceholderSub: return None
# 				return t
# 		return None
# 	def render(self,scope):
# 		# for zal in self.subs:#safemode
# 			# assert zal.bon == None or all(k == None for k in zal.bon.dat)#safemode
# 		rendercode
# 	# def postcompact(self,scope,subs):
# 	def subnames(self):
# 		return allvars([k.name for k in self.subs if type(k) is IndividualSub])
# 	def __len__(self):
# 		return len(self.subs)
# 	@debugdebug
# 	def equate(self,cno,other):
# 		i = 0
# 		for j in range(len(self.subs)):
# 			if type(self.subs[j]) is IndividualSub and self.subs[j].inherited: continue
# 			while type(other.subs[i]) is IndividualSub and other.subs[i].inherited and i<len(other.subs): i += 1
# 			if i>=len(other.subs): return False
# 			if type(self.subs[j]) is PlaceholderSub:
# 				if type(other.subs[i]) is not PlaceholderSub: return False
# 				else:
# 					i += 1
# 					continue

# 			yalda1 = None if self.subs[j].bon == None else ScopeIntroducer([self.subs[j].bon.dat[k] for k in range(j) if not (type(self.subs[k]) is IndividualSub and self.subs[k].inherited)])
# 			yalda2 = None if other.subs[i].bon == None else ScopeIntroducer([other.subs[i].bon.dat[k] for k in range(i) if not (type(other.subs[k]) is IndividualSub and other.subs[k].inherited)])
# 			# if self.subs[j].bon != None:#safemode
# 				# for k in range(j):#safemode
# 					# if type(self.subs[k]) is IndividualSub and self.subs[k].inherited: assert self.subs[j].bon.dat[k] == None#safemode
# 			# if other.subs[i].bon != None:#safemode
# 				# for k in range(i):#safemode
# 					# if type(other.subs[k]) is PlaceholderSub and other.subs[k].inherited: assert other.subs[i].bon.dat[k] == None#safemode
# 			gnj = copy.copy(self.subs[j])
# 			gnj.bon = yalda1
# 			jng = copy.copy(other.subs[i])
# 			jng.bon = yalda2
# 			if not gnj.equate(cno,jng): return False
# 			i += 1
# 		return i == len(other.subs)



# 		# gself = self.triangulate().onlyreal()
# 		# gother = other.triangulate().onlyreal()


# 		# equate is only called on verified

# 		# add debugdebug and make sure, then

# 		# if len(gself) != len(gother): return False
# 		# ja = [False]*len(gself)
# 		# jb = [False]*len(gself)
# 		# for a in range(len(gself)):
# 		# 	if gself.subs[a].name == None: continue
# 		# 	for b in range(len(gself)):
# 		# 		if gself.subs[a].name == gother.subs[b].name:
# 		# 			if not gself.subs[a].equate(cno,gother.subs[b]): return False
# 		# 			ja[a] = True
# 		# 			jb[b] = True
# 		# 			break
# 		# b=0
# 		# for a in range(len(gself)):
# 		# 	if ja[a]: continue
# 		# 	while jb[b]: b+=1
# 		# 	if not gself.subs[a].equate(cno,gother.subs[b]): return False
# 		# 	b+=1
# 		# return True


# 	postcompact is now verify
# 	def verify(self,indesc,carry=None):
 
# 		if type(carry) is not ObjKindTypeUnion:
# 			ErrorObject.fatal("Can't pair keyword arguments to static type.")

# 		return carry.verify(scope,nexself=SubsObject([k if not k.inherited else PlaceholderSub(k.name) for k in self.subs],pos=self),needscomplete=True,forceinheritance=True).subs


# # class StratSeries:
# 	# def __init__(self,data=None,flatdata=None,original=None):
# 	# 	self.data = [] if data == None else data
# 	# 	if self.data == []: flatdata = []
# 	# 	# for k in self.data: assert type(k) is ObjStrategy#safemode
# 	# 	self.verified = all(k.verified for k in self.data) and flatdata != None

# 	# 	self.flat = flatdata
# 	# 	# if self.flat != None:#safemode
# 	# 		# for k in self.flat:#safemode
# 	# 			# assert type(k) is ObjStrategy#safemode
# 	# 			# assert type(k.name) is str#safemode



# 	# 	# assert (self.flat == None) != (self.verified) #safemode
# 	# 	# if self.verified:#safemode
# 	# 		# for h in range(len(self.data)):#safemode
# 	# 			# for g in self.data[:h]:#safemode
# 	# 				# if g.name != None:#safemode
# 	# 					# if g.name == self.data[h].name:#safemode
# 	# 						# assert False#safemode
# 	# 	# if self.flat != None:#safemode
# 	# 		# for j in self.flat: assert j.verified#safemode
# 	# 		# for h in range(len(self.flat)):#safemode
# 	# 			# for g in self.flat[:h]:#safemode
# 	# 				# if g.name != None:#safemode
# 	# 					# assert g.name != self.flat[h].name#safemode


# 	# 	self.original = self.introducer() if original == None else original

# 	# def __repr__(self):
# 	# 	return ",".join([str(i) for i in self.data])
# 	# def wide_repr(self,depth):
# 	# 	return (",\n"+"\t"*depth).join([str(i) for i in self.data])
# 	# @debugdebug
# 	# def verify(self,indesc):
# 	# 	if self.verified: return self
# 	# 	zvn = []
# 	# 	zn = []
# 	# 	mmn = RenamerObject(scope)
# 	# 	for k in range(len(self.data)):
# 	# 		nm,nmmn = mmn.integrate(ScopeIntroducer(self.data[k].name))
# 	# 		pscope = StratSeries(zn,zvn,original=ScopeIntroducer(self.original.dat[:k]))


# 	# 		p = self.data[k].surfacerename(nm.dat).substitute(mmn,SubsObject()).verify(scope+pscope)
# 	# 		mmn=nmmn
# 	# 		zn.append(p)
# 	# 		zvn = zvn + p.split([k.name for k in scope.flat]+[k.name for k in zvn])
# 	# 	return StratSeries(zn,zvn,original=self.original)
# 	# @debugdebug
# 	# def substitute(self,revf,repl):
# 	# 	zn = []
# 	# 	zvn = []
# 	# 	mmn = revf

# 	# 	for k in range(len(self.data)):
# 	# 		zk = self.data[k].substitute(mmn,repl)
# 	# 		nname,mmn = mmn.integrate(ScopeIntroducer(self.data[k].name))
# 	# 		zn.append(zk.surfacerename(nname.dat))

# 	# 	if self.flat == None: return StratSeries(zn,original=self.original)

# 	# 	mmn = revf

# 	# 	for k in range(len(self.flat)):
# 	# 		zk = self.flat[k].substitute(mmn,repl)
# 	# 		nname,mmn = mmn.integrate(ScopeIntroducer(self.flat[k].name))
# 	# 		zvn.append(zk.surfacerename(nname.dat))

# 	# 	return StratSeries(zn,zvn,original=self.original)

# 	# def get(self,label):
# 	# 	for t in reversed(range(len(self.flat))):
# 	# 		if self.flat[t].name == label:
# 	# 			return self.flat[t]
# 	# 	return None

# 	# def introducer(self):
# 	# 	return ScopeIntroducer([k.name for k in self.data])
# 	# def refs(self,label):
# 	# 	# if label != None: assert type(label) is str#safemode
# 	# 	for k in self.data:
# 	# 		l = k.refs(label)
# 	# 		if l: return l
# 	# 		if ScopeIntroducer(k.name).contains(label): return False
# 	# 	return False
# 	# def __add__(self,other):
# 	# 	# assert type(other) is StratSeries#safemode
# 	# 	return StratSeries(self.data+other.data,self.flat+other.flat,original=ScopeIntroducer(self.original.dat+other.original.dat))

# 	# @debugdebug
# 	# def equate(self,cno,other):
# 	# 	if len(self.data) != len(other.data): return False
# 	# 	for i in range(len(self.data)):
# 	# 		if not self.data[i].equate(cno,other.data[i]): return False
# 	# 		cno = cno.sertequiv(ScopeIntroducer(self.data[i].name),ScopeIntroducer(other.data[i].name))
# 	# 		if cno == None: return False
# 	# 	return True

# visit each dualsubs constructor
# and each .data adn each .flat and each .original
# and each stratseries constructor.
# and prolly .variables

# carry pos through on dualsubs and subsobject

# class DualSubs:
# 	def __init__(self,variables=None,original=None,subs=None,exverified=False,pos=None):
# 		# for sp in variables:#safemode
# 			# assert type(sp) is ObjStrategy#safemode
# 		# if subs != None: assert type(subs) is SubsObject#safemode
# 		self.data = [] if variables == None else variables
# 		self.subs = subs if subs != None else SubsObject([PlaceholderSub(original.dat[n]) for n in range(len(variables))],exverified=True)
# 		self.original = self.introducer() if original == None else original
# 		# assert len(self.subs) == len(variables.data)#safemode
# 		# for j in range(len(self.subs)):#safemode
# 			# assert type(self.subs.subs[j]) is PlaceholderSub or not self.subs.subs[j].inherited#safemode
# 			# assert self.subs.subs[j].name == variables.original.dat[j]#safemode
# 		<><><><><>

# 		verified calculation must eval true if all nones are passed.

# 		self.verified = exverified and self.subs.verified and all(j.verified for j in self.variables)


# 		transferlines(self,pos)



# 	def __repr__(self):
# 		dh = ""
# 		for i in range(len(self.variables.data)):
# 			if type(self.subs.subs[i]) is PlaceholderSub:
# 				dh = dh + str(self.variables.data[i])+","
# 			else:
# 				hu = copy.copy(self.subs.subs[i])
# 				hu.name = None
# 				dh = dh + str(self.variables.data[i])+" = "+str(hu)+","
# 		if len(dh)>0: dh = dh[:-1]
# 		return dh
# 	def wide_repr(self,depth):
# 		dh = "\n"
# 		for i in range(len(self.variables.data)):
# 			if type(self.subs.subs[i]) is PlaceholderSub:
# 				dh = dh + "\t"*depth+str(self.variables.data[i])+",\n"
# 			else:
# 				hu = copy.copy(self.subs.subs[i])
# 				hu.name = None
# 				dh = dh + "\t"*depth+str(self.variables.data[i])+" = "+hu.wide_repr(depth+1)+",\n"
# 		if len(dh)>1: dh = dh[:-2]
# 		return dh

# 	@debugdebug
# 	def trimscript(self,a,b):
# 		zn  = []
# 		zvd = []
# 		c = 0
# 		for k in range(len(self.data)):
# 			if type(self.subs.subs[k]) is PlaceholderSub:
# 				if a<=c<b:
# 					zn.append(self.data[k])
# 					zvd.append(self.original.dat[k])
# 				c += 1
# 		return DualSubs(zn,ScopeIntroducer(zvd),exverified=self.verified,pos=self)

			
# 	@debugdebug
# 	def verify(self,scope,carry=None,nexself=None,needscomplete=False,forceinheritance=False):
# 		# if nexself != None: assert type(nexself) is SubsObject#safemode

# 		if carry!=None and not(type(carry) is ObjKindReferenceTree and carry.src == None and len(carry.args) == 0 and carry.name == "U"): ErrorObject.nonfatal("U =/= "+str(carry))

# 		def objstarter(goro,mmn,promotion=None):
# 			if promotion == None: promotion = []
# 			nanames = [promotion+[z] for z in range(len(self.subs.subs))]
# 			pure = []
# 			for k in range(len(self.subs.subs)):
# 				if type(self.subs.subs[k]) is PlaceholderSub:
# 					gna = PlaceholderSub(self.subs.subs[k].name,None if self.subs.subs[k].si == None else mmn.integrate(self.subs.subs[k].si)[0])
# 					gna.parallel = None
# 					pure.append(gna)
# 					continue
# 				if self.subs.subs[k].bon == None:
# 					tbo = None
# 					mmn2 = mmn
# 				else:
# 					tbo,mmn2 = mmn.integrate(self.subs.subs[k].bon)

# 				sksubs = []
# 				if self.subs.subs[k].downbon == None:
# 					tsi,mmn2 =  mmn2.integrate(self.subs.subs[k].si)
# 				else:
# 					tdb,mmn2 = mmn2.integrate(self.subs.subs[k].downbon.si)
# 					gre = DownBonObject(self.subs.subs[k].downbon.avail,tdb)
# 					tsi = gre.jsi()

# 					jdb = gre.jdb()
# 					# assert len(jdb) == len(self.variables.data[k].args.subs.subs)#safemode
# 					for n in range(len(jdb)):
# 						# assert (jdb.dat[n]==None) == (type(self.variables.data[k].args.subs.subs[n]) is PlaceholderSub)#safemode
# 						if type(self.variables.data[k].args.subs.subs[n]) is IndividualSub:
# 							sksubs = sksubs + self.variables.data[k].args.subs.subs[n].unwrapsubs(jdb.dat[n])

# 				yo = IndividualSub(self.subs.subs[k].name,tsi,self.subs.subs[k].obj.substitute(mmn2,SubsObject(sksubs)),bon=tbo,inherited=forceinheritance or self.subs.subs[k].inherited)
# 				yo.parallel = None
# 				pure.append(yo)
# 			return nanames,pure


# 		def assignvars(mot,subs,cars,spoken,mmn):
# 			# assert type(subs) is SubsObject#safemode
# 			# assert type(cars) is StratSeries#safemode


# 			def clarify(mog,subs,mmn):
# 				def internalplacehold(mog,pre=None):
# 					if pre == None: pre = ScopeIntroducer([])
# 					if isinstance(mog,list):
# 						i = []
# 						for f in range(len(mog)):
# 							i.append(internalplacehold(mog[f]))
# 						return (pre,i,None)
# 					nyop = PlaceholderSub(mog,pre)
# 					nyop.parallel = None
# 					return nyop
# 				def internalclarify(obj,mog,trail,inh,pre=None,pb=None):
# 					if pre == None: pre = ScopeIntroducer([])
# 					if isinstance(mog,list):
# 						i = []
# 						for f in range(len(mog)):
# 							i.append(internalclarify(obj,mog[f],trail+[(f,len(mog))],inh))
# 						return (pre,i,pb)
# 					jog = obj
# 					for s in trail:
# 						jog = ObjKindReferenceTree(src=jog,name=s,verprot=0)
# 					nyop = IndividualSub(mog,pre,jog,bon=pb,exverified=True)
# 					nyop.parallel = None
# 					return nyop

# 				ju = [k for k in subs.subs if not k.inherited]
# 				while len(mog) != len(ju) and len(mog) == 1: mog = mog[0]
# 				while len(mog) != len(ju) and len(ju) == 1: mog = [mog]

# 				if len(mog) == len(ju):
# 					jak = []
# 					for k in range(len(mog)):
# 						if type(ju[k]) is PlaceholderSub:
# 							if ju[k].si == None:
# 								tsi = None
# 							else:
# 								tsi,mmn2 =  mmn.integrate(ju[k].si)
# 							jak.append(internalplacehold(mog[k],pre=tsi))
# 							continue

# 						if ju[k].bon == None:
# 							tbo = None
# 							mmn2 = mmn
# 						else:
# 							tbo,mmn2 = mmn.integrate(ju[k].bon)
# 						if ju[k].downbon == None:
# 							tsi,mmn2 =  mmn2.integrate(ju[k].si)
# 						# else: assert False#safemode
# 						if isinstance(mog[k],list):
# 							if type(ju[k].obj) is not ObjKindUnionSet:
# 								jak.append(internalclarify(ju[k].obj.substitute(mmn2,SubsObject()),mog[k],[],pre=tsi,pb=tbo))
# 							else:
# 								sin = clarify(mog[k],ju[k].obj.subs,mmn2)
# 								mog[k] = sin[1]
# 								jak.append((tsi,sin[0],tbo))
# 						else:
# 							nyop = IndividualSub(mog[k],tsi,ju[k].obj.substitute(mmn2,SubsObject()),bon=tbo)
# 							nyop.parallel = None
# 							jak.append(nyop)
# 					return (jak,mog)
# 				else: ErrorObject.fatal("Invalid unwrapping scheme")

# 			def satisfied(spoken):
# 				if isinstance(spoken,list):
# 					return all(satisfied(f) for f in spoken)
# 				return spoken
# 			def firstnamed(mot,spoken,label,cars):
# 				for f in range(len(mot)):
# 					if isinstance(mot[f],list):
# 						if spoken[f] == True: continue
# 						if spoken[f] == False:
# 							tentspok = [False]*len(mot[f])
# 							assignvars(cars.data[f].type.subs.variables.original.dat,cars.data[f].type.subs.subs,cars.data[f].type.subs.variables,tentspok,None)
# 							k = firstnamed(mot[f],tentspok,label,cars.data[f].type.subs.variables)
# 							if k:
# 								spoken[f] = tentspok
# 								return [f] + k
# 						else:
# 							k = firstnamed(mot[f],spoken[f],label,cars.data[f].type.subs.variables)
# 							if k: return [f]+k
# 					elif mot[f] == label and not spoken[f]:
# 						spoken[f] = True
# 						return [f]
# 			def ropnames(mot,spoken,scrubs):
# 				if isinstance(scrubs,list):
# 					return [ropnames(mot,spoken,f) for f in scrubs]
# 				if scrubs == None:
# 					for j in range(len(spoken)):
# 						if not satisfied(spoken[j]):
# 							spoken[j] = True
# 							return [j]
# 					ErrorObject.fatal("Too many arguments.")
# 				k = firstnamed(mot,spoken,scrubs,cars)
# 				if k: return k
# 				ErrorObject.fatal("Unknown argument specified or already specified: "+scrubs)
# 			def undopath(path,spoken):
# 				# assert all(type(k) is int for k in path)#safemode
# 				if spoken == True or spoken == False: return
# 				if len(path) == 1:
# 					spoken[path[0]] = False
# 				else:
# 					undopath(path[1:],spoken[path[0]])
# 			def undopaths(path,spoken):
# 				if all(type(k) is int for k in path):
# 					undopath(path,spoken)
# 				else:
# 					for r in path: undopaths(r,spoken)
# 			def remplace(nanames,subs,spoken):
# 				for f in range(len(nanames)):
# 					if type(subs.subs[f]) is PlaceholderSub:
# 						undopaths(nanames[f],spoken)
# 					elif not (len(nanames[f])>0 and isinstance(nanames[f][0],int)) and type(subs.subs[f].obj) is ObjKindUnionSet:
# 						remplace(nanames[f],subs.subs[f].obj.subs,spoken)

# 			mok = [copy.deepcopy(k.name) for k in subs.subs]
# 			if mmn != None:
# 				pure,mok = clarify(mok,subs,mmn)
# 			na = ropnames(mot,spoken,mok)
# 			remplace(na,subs,spoken)
# 			if mmn == None: return na
# 			return (na,pure)

# 		def allpop(mot,spoken,types):
# 			for f in range(len(mot)):
# 				if isinstance(mot[f],list):
# 					allpop(mot[f],spoken[f],types.data[f].type.subs.variables)

# 				elif not spoken[f] and not (type(types.data[f].type) is ObjKindTypeUnion and types.data[f].type.subs.lenavail() == 0):
# 					if mot[f]==None: ErrorObject.fatal("Missing positional argument.")
# 					ErrorObject.fatal("Missing named argument: "+str(mot[f]))


# 		def repltips(nanames,yoks,sem,ulsem,seltrail,repl):
# 			for j in range(len(yoks)):
# 				if isinstance(yoks[j],tuple):
# 					yad = [] if yoks[j][2]==None else yoks[j][2].allvars()
# 					replall(nanames[j],yoks[j][1],sem+yad+yoks[j][0].allvars(),ulsem,seltrail,repl)
# 				elif nanames[j][:len(seltrail)] == seltrail:
# 					pcast = yoks[j].substitute(RenamerObject(sem),repl)
# 					pcast.parallel = None if yoks[j].parallel == None else yoks[j].parallel.substitute(RenamerObject(ulsem),repl)
# 					yoks[j] = pcast
# 		def replall(yoks,sem,ulsem,repl):
# 			for j in range(len(yoks)):
# 				if isinstance(yoks[j],tuple):
# 					jsem = sem
# 					neb = None
# 					if yoks[j][2] != None:
# 						neb,jsem = jsem.integrate(yoks[j][2])
# 					nes,jsem = jsem.integrate(yoks[j][0])
# 					replall(yoks[j][1],jsem,ulsem,repl)
# 					yoks[j] = (nes,yoks[j][1],neb)
# 				else:
# 					pcast = yoks[j].substitute(sem,repl)
# 					pcast.parallel    = None if yoks[j].parallel == None    else yoks[j].parallel.substitute(ulsem,repl)
# 					yoks[j] = pcast
# 		def recurse(scope,nanames,cars,yoks,trail,args,arsem,downrun,downback,pos=None):
# 			# print("got arsem: ",arsem)
# 			# assert len(yoks) == len(nanames)#safemode
# 			def firstfounddec(nanames,pattern):
# 				if len(nanames)>0 and isinstance(nanames[0],int):
# 					if nanames == pattern: return False
# 					if nanames[:len(pattern)] == pattern: return True
# 					return None
# 				for j in nanames:
# 					k = firstfounddec(j,pattern)
# 					if k == None: continue
# 					return k
# 			zn = []
# 			runsubs = downrun
# 			backtf  = downback
# 			outsubs = []
# 			mmn = RenamerObject(scope)
# 			psem = arsem
# 			nyargs = args.bgroup(psem)
# 			for z in range(len(cars.data)):
# 				pscope = scope+StratSeries(zn,znflat,original=ScopeIntroducer(cars.original.dat[:z]))
# 				shiiiiit<><><><><><><>

# 				nname,mmn2 = mmn.integrate(ScopeIntroducer(cars.data[z].name))
# 				zaku = cars.data[z].substitute(mmn,SubsObject(runsubs)).surfacerename(nname.dat)
# 				# assert zaku.verified#safemode


# 				pargs = args+zaku.args
# 				# assert pargs.verified#safemode
# 				def findindsub(nanames,yoks,cargs,sem,j1cu,illegal):
# 					for j in range(len(nanames)):
# 						if type(yoks[j]) is PlaceholderSub: continue
# 						if type(yoks[j]) is IndividualSub:
# 							ybon = yoks[j].bon
# 						else:
# 							ybon = yoks[j][2]
# 						ysem = sem
# 						jat1 = j1cu
# 						silleg = illegal
# 						if ybon != None:
# 							# assert j == len(ybon.dat)#safemode
# 							for k in range(j):
# 								ysem = ysem + allvars(ybon.dat[k])
# 								if type(yoks[k]) is not IndividualSub or yoks[k].parallel == None:
# 									silleg = silleg + allvars(ybon.dat[k])
# 								else:
# 									jat1 = jat1 + yoks[k].unwrapsubs(ybon.dat[k])
# 						if type(yoks[j]) is tuple:
# 							ysem = ysem + yoks[j][0].allvars()
# 						else:
# 							ysem = ysem + yoks[j].si.allvars()
# 							if nanames[j] == trail+[z] and yoks[j].si != None:
# 								if len(cargs)+len(yoks[j].si.dat) != pargs.lenavail():
# 									ErrorObject.fatal("wrong number of introduced arguments here.")
# 						if nanames[j] == trail+[z] and type(yoks[j]) is IndividualSub:
# 							for u in silleg:
# 								if yoks[j].obj.refs(u):
# 									ErrorObject.fatal("The usage of the following variable violates the well-ordering property: "+str(u))
# 							# RenamerObject(psem+allvars(cargs+yoks[j].si.dat))#safemode
# 							splitter,nexsem = RenamerObject(psem + pargs.semavail().allvars()).integrate(ScopeIntroducer(cargs+yoks[j].si.dat))
# 							jat2 = pargs.bgroup(psem).unwrapsubs(splitter)#<-- unwrapping over the wrong thing?
# 							nobj = yoks[j].obj.substitute(RenamerObject(ysem),SubsObject(jat1)).substitute(nexsem,SubsObject(jat2))
# 							return (nobj,yoks[j].inherited)
# 						if type(yoks[j]) is tuple:
# 							k = findindsub(nanames[j],yoks[j][1],cargs+yoks[j][0].dat,   ysem    ,jat1,silleg     )
# 							if k: return k
# 				if firstfounddec(nanames,trail+[z]):
# 					nespoke = [False]*len(zaku.type.subs.variables.data)
# 					nanam,nyoks = objstarter(zaku.type.subs,RenamerObject(psem),promotion=trail+[z])
# 					# bbl = []
# 					# nanam,nyoks = assignvars(zaku.type.subs.variables.original.dat,zaku.type.subs.subs,zaku.type.subs.variables,nespoke,RenamerObject(psem),promotion=trail+[z],dbl=bbl,inherited=forceinheritance,rlayer=True)
# 					zot = recurse(pscope+zaku.args.variables,[nanam,nanames],zaku.type.subs.variables,[(zaku.args.semavail(),nyoks,None),(ScopeIntroducer([]),yoks,None)],trail+[z],pargs,psem,runsubs,backtf,pos=zaku.type)
# 					denizen = ObjStrategy(name=zaku.name,ty=zaku.type,args=pargs,exverified=True).bgroup(psem+allvars(zaku.name),zaku.name)
# 					nsvi,remmn = RenamerObject(psem+allvars(zaku.name)).integrate(zaku.type.subs.variables.introducer())
# 					whoas = denizen.unwrapsubs(nsvi.dat)
# 					replall(yoks,remmn,remmn,SubsObject(whoas))
# 					zaku = ObjStrategy(args=zaku.args,ty=ObjKindTypeUnion(subs=zot,exverified=True),name=zaku.name,exverified=True)
# 					# assert zaku.verified#safemode
# 				def blendsub(nanames,yoks,cargs,mmn,xsi,moto):
# 					for j in range(len(nanames)):
# 						if type(yoks[j]) is IndividualSub and yoks[j].bon != None:
# 							tbo,mmn2 =  mmn.integrate(yoks[j].bon)
# 						elif type(yoks[j]) is tuple and yoks[j][2] != None:
# 							tbo,mmn = mmn.integrate(yoks[j][2])
# 						else:
# 							tbo = None
# 							mmn2 = mmn
# 						if type(yoks[j]) is tuple:
# 							ltsi = len(cargs)+len(yoks[j][0].dat)
# 							tsi,mmn2 = mmn2.integrate(yoks[j][0])
# 							blendsub(nanames[j],yoks[j][1],cargs+tsi.dat,mmn2,xsi,moto)
# 							cool = False
# 							for jan in yoks[j][1]:
# 								if type(jan) is tuple: break
# 								if jan.parallel == None: break
# 							else:
# 								for jan in yoks[j][1][1:]:
# 									if not jan.parallel.args.trimscript(0,ltsi).equate(CrossNameObject(),yoks[j][1][0].parallel.args.trimscript(0,ltsi)):
# 										ErrorObject.fatal("Attempted to merge incompatable variables: "+str(jan.parallel.args.trimscript(0,ltsi))+"=/="+str(yoks[j][1][0].parallel.args.trimscript(0,ltsi)))
# 								cool = True
# 							if not cool: continue
# 							radj = RenamerObject(mmn2.s)
# 							durup = []
# 							dunuk = []
# 							for y in yoks[j][1]:
# 								# assert y.expected.verified#safemode
# 								# assert y.verified#safemode
# 								# assert y.parallel.verified#safemode
# 								okk,radj = radj.integrate(ScopeIntroducer(None))

# 								xnaf = ObjStrategy(name=zaku.name,args=y.parallel.args.trimscript(len(cargs),y.parallel.args.lenavail()),ty=y.parallel.type,exverified=True)
# 								# assert xnaf.verified#safemode

# 								duc = copy.copy(xnaf).substitute(radj,SubsObject())
# 								duc.name = okk.dat
# 								durup.append(duc)
# 								duc = copy.copy(y).substitute(radj,SubsObject())
# 								duc.name = okk.dat
# 								dunuk.append(duc)

# 							tytype = ObjKindTypeUnion(variables=StratSeries(durup,durup),exverified=True)
# 							# assert tytype.verified#safemode
# 							obj = ObjKindUnionSet(subs=SubsObject(dunuk,exverified=True),verprot=1)
# 							# assert obj.verified#safemode
# 						else:
# 							ltsi = pargs.lenavail()
# 							if nanames[j] != trail+[z]:
# 								pcast = yoks[j].substitute(mmn,SubsObject())
# 								pcast.parallel = None if yoks[j].parallel == None else yoks[j].parallel.substitute(RenamerObject(psem),SubsObject())
# 								yoks[j] = pcast
# 								continue
# 							tytype = zaku.type
# 						prez = pargs.trimscript(0,len(cargs)).bgroup(psem+allvars(cargs),cargs)
# 						# assert tytype.verified#safemode
# 						xnaf = ObjStrategy(name=zaku.name,args=pargs,ty=tytype,exverified=True)
# 						mojo,ren = RenamerObject(psem+allvars(cargs)).integrate(ScopeIntroducer(pargs.semavail().dat[:len(cargs)]))
# 						nexpect = ObjStrategy(name=zaku.name,args=pargs.trimscript(len(cargs),ltsi),ty=tytype,exverified=True).substitute(ren,SubsObject(prez.unwrapsubs(mojo)))
# 						if type(yoks[j]) is not tuple:
# 							btsi,ren = RenamerObject(psem+allvars(cargs)).integrate(ScopeIntroducer(args.semavail().dat+xsi.dat))
# 							tsi = ScopeIntroducer(btsi.dat[len(cargs):])
# 							obj = moto.substitute(ren,SubsObject(prez.unwrapsubs(btsi.dat[:len(cargs)])))
# 						yoks[j] = IndividualSub(None,tsi,obj,expected=nexpect,exverified=True)
# 						# assert yoks[j].verified#safemode
# 						yoks[j].parallel = xnaf
# 				moto = findindsub(nanames,yoks,[],psem,[],[])
# 				inh = False
# 				if moto != None: moto,inh = moto
# 				if moto != None:
# 					# ErrorObject.takeblame(moto)
# 					# ErrorObject.nonfatal(str(zaku.type))
# 					moto = moto.verify(pscope+zaku.args.variables,zaku.type)
# 				if type(zaku.type) is ObjKindTypeUnion:
# 					if moto != None:
# 						zaku = ObjStrategy(args=zaku.args,ty=zaku.type.verify(pscope+zaku.args.variables,nexself=SubsObject(IndividualSub(None,pargs.semavail(),moto).unwrapsubs([None]*zaku.type.subs.lenavail())),needscomplete=True),name=zaku.name,exverified=True)
# 						moto = None
# 					if zaku.type.subs.lenavail() == 0:
# 						moto = ObjKindUnionSet(subs=zaku.type.subs.subs,verprot=1)
# 						# assert moto.verified#safemode
# 				jazak = zaku.substitute(RenamerObject([p.name for p in pscope.flat]),SubsObject(backtf))
# 				if moto == None:
# 					atrz = ObjStrategy(name=zaku.name,ty=zaku.type,args=pargs,exverified=True).bgroup(psem+allvars(zaku.name),zaku.name)
# 					moto = atrz.obj
# 					# assert args.semavail().dat == atrz.si.dat[:len(args.semavail().dat)]#safemode
# 					xsi = ScopeIntroducer(atrz.si.dat[len(args.semavail().dat):])
# 					outsubs.append(PlaceholderSub(cars.original.dat[z]))
# 				else:
# 					assert moto.verified
# 					assert zaku.verified
# 					xsi = zaku.args.semavail()
# 					myoto = moto.substitute(RenamerObject(psem+pargs.variables.introducer().allvars()),SubsObject(backtf))
# 					outsubs.append(IndividualSub(cars.original.dat[z],zaku.args.semavail(),myoto,bon=None if needscomplete else ScopeIntroducer([k.name for k in zn]),expected=jazak,exverified=True,inherited=inh))
# 					# assert outsubs[-1].verified#safemode
# 				psem = psem+allvars(zaku.name)
# 				blendsub(nanames,yoks,[],RenamerObject(psem),xsi,moto)
# 				# assert zaku.verified#safemode
# 				runsubs = runsubs + IndividualSub(zaku.name,xsi,moto).unwrapsubs(zaku.name)
# 				backtf  = backtf  + [DowngradeSub(nyargs,zz) for zz in allvars(zaku.name)]
# 				zn.append(jazak)

# 				mmn = mmn2
# 			# assert len(outsubs) == len(zn)#safemode
# 			zalog = DualSubs(zn,original=cars.original,SubsObject(outsubs,exverified=True),exverified=True,pos=pos)
# 			# assert zalog.verified#safemode
# 			return zalog

# 		if nexself == None:
# 			if all(type(h) is PlaceholderSub for h in self.subs.subs):
# 				return DualSubs(self.variables,exverified=True,pos=self)

# 		nanames,pure = objstarter(self,RenamerObject(scope))
# 		spoken  = [type(j) is IndividualSub for j in self.subs.subs]
# 		# spoken = [False]*len(self.variables.data) 
# 		# bbl = []
# 		# nanames,pure = assignvars(self.variables.original.dat,self.subs,self.variables,spoken,RenamerObject(scope),dbl=bbl,inherited=forceinheritance,rlayer=True)
# 		if nexself != None:
# 			nunama,nupure = assignvars(self.variables.original.dat,nexself,self.variables,spoken,RenamerObject(scope))
# 			nanames = [nanames,nunama]
# 			pure = [(ScopeIntroducer([]),pure,None),(ScopeIntroducer([]),nupure,None)]
# 		if needscomplete: allpop(self.variables.original.dat,spoken,self.variables)
# 		return recurse(scope,nanames,self.variables,pure,[],DualSubs(),[k.name for k in scope.flat],[],[],self)


# 	@debugdebug
# 	def substitute(self,revf,repl):
# 		vasr = self.variables.substitute(revf,repl)

# 		god <><><><><>

# 		null,mmn = revf.integrate(self.variables.introducer())
# 		subs = self.subs.substitute(mmn,repl)
# 		return DualSubs(vasr,subs,exverified=self.verified,pos=self)
# 	def refs(self,label):
# 		l = self.variables.refs(label)
# 		if l: return l
# 		return self.subs.refs(label)
# 	def __add__(self,other):
# 		# assert type(other) is DualSubs#safemode
# 		return DualSubs(self.variables+other.variables,ScopeIntroducer(self.original.dat+other.original.dat),self.subs+other.subs,exverified=self.verified and other.verified)

# 	@debugdebug
# 	def equate(self,cno,other):
# 		a = self.availvariables()
# 		b = other.availvariables()
# 		if len(a) != len(b): return False
# 		return all(a[c].equate(cno,b[c]) for c in range(len(a)))
# 		# vno = cno.sertequiv(self.variables.original,other.variables.original)
# 		# return self.variables.equate(cno,other.variables) and self.subs.equate(vno,other.subs)

# 	def availvariables(self):
# 		# assert self.verified#safemode

# 		# for k in range(len(self.variables.data)):#safemode
# 			# if type(self.subs.subs[k]) is IndividualSub:#safemode

# 				# for o in self.variables.data[k+1:]:#safemode
# 					# if o.refs(self.variables.data[k].name):#safemode
# 						# assert False#safemode
# 		res = []
# 		for t in range(len(self.variables.data)):
# 			if type(self.subs.subs[t]) is PlaceholderSub:
# 				res.append(self.variables.data[t])
# 		return res
# 	def lenavail(self):
# 		l=0
# 		for t in self.subs.subs:
# 			if type(t) is PlaceholderSub:
# 				l = l + 1
# 		return l
# 	def semavail(self):

# 		return ScopeIntroducer([self.variables.data[k].name for k in range(len(self.variables.data)) if type(self.subs.subs[k]) is PlaceholderSub])

# 	@debugdebug
# 	def bgroup(self,semscope,mog=None,src=None,prep=None):
# 		# assert self.verified#safemode
# 		# RenamerObject(semscope)#safemode
# 		if mog == None:
# 			mog = self.variables.introducer()
# 			# RenamerObject(mog.allvars())#safemode
# 			semscope = semscope + mog.allvars()#<---- yeesh... wouldnt you be adding these as you go? might need a better strategy...
# 			# RenamerObject(semscope)#safemode

# 		if type(mog) is ScopeIntroducer: mog = mog.dat
# 		# assert mog != None#safemode

# 		# assert type(mog) is not str#safemode
# 		if len(mog) != len(self.variables.data):
# 			ErrorObject.fatal("Mechanical error (subside): Wrong number of arguments for unwrap.")
# 		voexsubs = SubsObject()
# 		jan  = []
# 		semscope2 = RenamerObject(semscope)

# 		for i in range(len(self.variables.data)):
# 			if type(self.subs.subs[i]) is IndividualSub:
# 				# print("----->",i,[type(k) for k in self.subs.subs],voexsubs.subs,"[][][]",self)

# 				yel = self.subs.subs[i]
# 				yelsi = yel.si
# 				if yel.bon != None:
# 					nunwrap,semscope3 = semscope2.integrate(yel.bon)
# 					yelsi,semscope3 = semscope3.integrate(yel.si)
# 					yel = yel.substitute(semscope3,SubsObject(SubsObject(jan).unwrapsubs(nunwrap)))

# 				nu = IndividualSub(self.variables.original.dat[i],yelsi,yel.obj,expected=self.variables.data[i].substitute(semscope2,voexsubs),exverified=True,inherited=True)

# 			else:
# 				# print("dpomg:",self.variables.data[i],semscope2,semscope,voexsubs)
# 				myst = (i,len(self.variables.data)) if mog[i]==None else mog[i]
# 				nu = self.variables.data[i].substitute(semscope2,voexsubs).bgroup(semscope,myst,ovname=self.variables.original.dat[i],src=src,prep=prep)

# 				nzaka,semscope2 = semscope2.integrate(ScopeIntroducer(self.variables.data[i].name))
# 				voexsubs = voexsubs + SubsObject(nu.unwrapsubs(nzaka.dat))
# 				# voexsubs.substitute(DebuggerRenamerObject(semscope),SubsObject())

# 			jan.append(nu)

# 		# for j in jan:#safemode
# 			# assert j.verified#safemode
# 		return SubsObject(jan,exverified=True)







# #-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=




# oneoff = True
# totruntime = 0


# class ObjStrategy:
# 	def __init__(self,args=None,ty=None,name=None,pos=None,exverified=False):
# 		if type(name) is ScopeIntroducer: name = name.dat
# 		self.args = DualSubs() if args == None else args
# 		self.name = name
# 		self.type = ty
# 		# assert self.name == None or type(self.name) is str or type(self.name) is list#safemode
# 		transferlines(self,pos)
# 		# assert issubclass(type(self.type),ObjKind)#safemode
# 		# assert type(self.args) is DualSubs#safemode
# 		self.verified = exverified and self.type.verified and self.args.verified
# 	def __repr__(self):
# 		if len(self.args.variables.data) != 0:
# 			if self.name != None: return "["+str(self.args)+"]"+str(self.name)+":"+str(self.type)
# 			else: return "["+str(self.args)+"]"+str(self.type)
# 		else:
# 			if self.name != None: return str(self.name)+":"+str(self.type)
# 			else: return str(self.type)
# 	@debugdebug
# 	def verify(self,indesc,carry=None):


# 		if carry!=None and not(type(carry) is ObjKindReferenceTree and carry.src == None and len(carry.args) == 0 and carry.name == "U"): ErrorObject.nonfatal("U =/= "+str(carry))

# 		global oneoff
# 		sarg = oneoff
# 		oneoff = False

# 		ErrorObject.takeblame(self)
# 		if self.verified: return self

# 		if sarg:print("I MEAN ALRIGHT")
# 		if sarg:prestart = time.time()
# 		verargs = self.args.verify(indesc)
# 		if sarg:start = time.time()


# 		sresressres = ObjStrategy(
# 			args=verargs,
# 			ty=self.type.verify(indesc.append(verargs),ObjKindReferenceTree(name="U",verprot=2)),
# 			name=self.name,
# 			pos=self,
# 			exverified=True
# 		)
# 		if sarg:end = time.time()
# 		if sarg:print("TIME TAKEN: ",start - prestart)
# 		if sarg:print("TIME TAKEN: ",end - start)

# 		return sresressres
# 	@debugdebug
# 	def substitute(self,revf,repl):
# 		if len(revf.data) == 0 and len(repl) == 0: return self
# 		null,mmn = revf.integrate(self.args.variables.introducer())
# 		return ObjStrategy(args=self.args.substitute(revf,repl),ty=self.type.substitute(mmn,repl),name=self.name,pos=self,exverified=self.verified)
# 	def refs(self,label):
# 		l = self.args.refs(label)
# 		if l: return l
# 		return not self.args.variables.introducer().contains(label) and self.type.refs(label)
# 	def surfacerename(self,newname):
# 		if newname == self.name: return self
# 		# assert newname == None or type(newname) is str#safemode
# 		y = copy.copy(self)
# 		y.name = newname
# 		return y
# 	@debugdebug
# 	def split(self,semscope):
# 		if type(self.name) is str: return [self]
# 		return self.bgroup(semscope+allvars(self.name),self.name).seekstrat(self.name)

# 	@debugdebug
# 	def bgroup(self,semscope,mog,ovname=None,src=None,prep=None):
# 		# assert self.verified#safemode
# 		if type(mog) is ScopeIntroducer: mog = mog.dat
# 		if prep == None: prep = SubsObject()
# 		# assert mog != None#safemode
# 		# assert self.name != None#safemode
# 		ErrorObject.takeblame(self)

# 		nargs = self.args.substitute(RenamerObject(semscope),SubsObject())
# 		pushy = nargs.bgroup(semscope)

# 		if type(mog) is str:
# 			yat = ObjKindReferenceTree(src=src,name=mog,args=prep+pushy,verprot=2-int(src!=None))
# 			# assert yat.verified#safemode
# 		else:
# 			pas,rens = RenamerObject(semscope).integrate(self.args.variables.introducer())

# 			if type(self.type) is not ObjKindTypeUnion:
# 				ErrorObject.fatal("Mechanical error (subside): Non-unionset unwrapped in given paramter for eval. mog:"+str(mog)+" ,self: "+str(self))
# 			pyz = self.type.subs.substitute(rens,SubsObject()).bgroup(rens.s,mog,src=src,prep=prep+pushy)
# 			# assert pyz.verified#safemode

# 			yat = ObjKindUnionSet(subs=pyz,verprot=1)

# 		zador = IndividualSub(ovname,nargs.semavail(),yat,expected=self,exverified=True)
# 		# assert zador.verified#safemode
# 		return zador




# 	@debugdebug
# 	def equate(self,cno,other):
# 		if not self.args.equate(cno,other.args): return False
# 		kkj = cno.sertequiv(self.args.variables.introducer(),other.args.variables.introducer())
# 		if kkj == None: return False
# 		return self.type.equate(kkj,other.type)





# #	code form
# #review prints,and assertions, and try/catches, and raises, and returns
# #check all returns and args to see if its the wrapping class or just the internal, and establish some kind of convention
# #you could do stuff like overriding lists to make encapsulators look nicer... probably in another version


# #	verification
# #do a statement verify after




# #   possible features
# #operator overloading?

# #concatenation operator &. it takes (a,b) & (a,b,c) becomes (a,b,a,b,c) and is evaluated before unwrapsubs.
# #automatic naming operator *. it sets the name to the name of the thing that gets substituted in.
# #composite type inference.





# #add an operator that can make variables silent.


# #	to implement

# #maybe try to remember the number of arguments each SI has on doubleback.
# #separate property for whether it was simplified with type.
# # better error messages (ones that show the correct signature when the sig isnt fulfilled.)



# # you need substitute to work correctly with ObjKindWildcard

# #stratseries.flat is checked to be flat, right?


# # equate forgets scope.stuff. remember and come up with a different operational modus to make that shit work better.


