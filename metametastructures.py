


from .debugging import debugdebug




# def forceimport(module_name, *names):
#     for name in names:
#         globals()[name] = getattr(sys.modules[module_name], name)


class ObjKind: pass



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
	def verify(self,scope,carry,force=True):
		ErrorObject.takeblame(self)
		if carry!=None and not(type(carry) is ObjKindReferenceTree and carry.src == None and len(carry.args) == 0 and carry.name == "U"): ErrorObject.nonfatal("U =/= "+str(carry))
		if self.verified: return self
		yu = self.src.verify(scope,None,force=force)
		if type(yu) is ObjKindTemplateHolder:
			return ObjKindTemplateHolder(src=yu.src,subs=yu.subs+self.subs,pos=self,exverified=True)

		if type(yu) is ObjKindTypeUnion:
			return yu.compactify(scope,self.subs,force=force)

		if type(yu) is ObjKindReferenceTree:
			return ObjKindTemplateHolder(src=yu,subs=self.subs,pos=self,exverified=True)

		ErrorObject.fatal("Substitution is only supported on unions.")
	@debugdebug
	def substitute(self,revf,repl):
		return ObjKindTemplateHolder(self.src.substitute(revf,repl),self.subs.substitute(revf,repl),pos=self,exverified=self.verified)
	def refs(self,label):
		l = self.src.refs(label)
		if l: return l
		return self.subs.refs(label)
	@debugdebug
	def equate(self,cno,other,force=False):
		if type(other) is ObjKindWildcard: return other.equate(cno.flip(),self,force=force)
		if type(other) is not ObjKindTemplateHolder: return False
		return self.src.equate(cno,other.src,force=force) and self.subs.equate(cno,other.subs,force=force)
	def gentype(self,scope,force=True):
		return ObjKindReferenceTree(name="U",verprot=2)



class ObjKindReferenceTree(ObjKind):
	def __init__(self,args=None,src=None,name=None,pos=None,verprot=None):
		if args == None:
			self.args = SubsObject()
		elif type(args) is SubsObject:
			self.args = args
		else:
			self.args = SubsObject([IndividualSub(None,ScopeIntroducer([]),args[z]) for z in range(len(args))])

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

		# assert type(self.name) is str or (type(self.name) is tuple and src!=None)#safemode

		self.verprot = verprot if self.verified else None


	def __repr__(self):
		lab = ""
		if self.src != None: lab = str(self.src)+"."
		lab = lab+str(self.name)
		blad = []
		for u in self.args.subs:
			if type(u) is PlaceholderSub: continue
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
			if type(u) is PlaceholderSub: continue
			sna = copy.copy(u)
			sna.name = None
			blad.append(sna)

		if len(self.args) != 0:
			lab = lab+"("+SubsObject(blad).oblong_repr(depth+1)+")"
		return lab
	@debugdebug
	def verify(self,scope,carry,force=True):
		ErrorObject.takeblame(self)
		# ErrorObject.nonfatal("X")

		if self.verified: return self
		# 	errors.nonfatal("X")
		if self.src == None and len(self.args) == 0 and self.name == "U":
			if type(carry) is ObjKindReferenceTree and carry.src == None and len(carry.args) == 0 and carry.name == "U":
				return ObjKindReferenceTree(name="U",verprot=2)
		if self.src != None:
			poc = self.src.verify(scope,None,force=force)
			if type(poc) is ObjKindReferenceTree or type(poc) is ObjKindTemplateHolder:
				if type(poc) is ObjKindTemplateHolder: poc=poc.src
				# assert type(poc) is ObjKindReferenceTree#safemode

				gmo = poc.gentype(scope,force=force)
				if type(gmo) is not ObjKindTypeUnion: ErrorObject.fatal("Cannot access property of a variable of this type.")

				fulob = gmo.subs.bgroup([s.name for s in scope.flat],gmo.subs.variables.original,src=poc)
				t=None
				# print("fulob",fulob)
				# print("logging",gmo.subs.variables.original)
				if type(self.name) is tuple:
					ha = fulob.onlyreal().subs
					if len(ha) != self.name[1]: ErrorObject.fatal("Incorrect unwrap length...")
					t = ha[self.name[0]]
				else:
					for nas in fulob.seekstrat(gmo.subs.variables.original):
						if nas.name == self.name:
							t=nas
				if t == None: ErrorObject.fatal("Property not found:"+str(self.name))

				sgig = self.arginternal(scope,t,carry,force=force)

				return ObjKindReferenceTree(src=poc,args=sgig,name=self.name,pos=self,verprot=1)
			# assert type(poc) is ObjKindTypeUnion or type(poc) is ObjKindUnionSet#safemode
			blcarry = poc.get(self.name)
			if blcarry == None:
				ErrorObject.fatal("No such property exists or the property exists but was not defined.")
			if blcarry.bon != None and not all(k == None for k in blcarry.bon.dat):
				ErrorObject.fatal("The property accessed here is dependently typed and refers to a variable that is unspecified. (Property cannot be used in static context.)")
			t = blcarry.expected
			if t == None:
				ErrorObject.fatal("Unable to infer type for:"+str(self.name))

			# substitute t and blcarry.obj.

			nukl,nreu = RenamerObject(scope).integrate(blcarry.si)
			duke = self.arginternal(scope,t,carry,force=force)
			mode = blcarry.obj.substitute(nreu,SubsObject(duke.unwrapsubs(nukl,onlyavailable=True)))

			return mode.verify(scope,carry,force=force)
		t = scope.get(self.name)
		if t == None:
			ErrorObject.fatal("Referenced variable not in scope:"+self.name)

		snot = self.arginternal(scope,t,carry,force=force)
		return ObjKindReferenceTree(args=snot,name=self.name,pos=self,verprot=2)
	def gentype(self,scope,force=True):
		if self.src != None: return None


		t = scope.get(self.name)
		if t == None:
			ErrorObject.fatal("Referenced variable not in scope:"+self.name)
		# assert self.verified#safemode

		null,nreu = RenamerObject(scope).integrate(t.args.variables.introducer())
		exptyoe = t.type.substitute(nreu,SubsObject(self.args.unwrapsubs(null)))
		exptyoe = exptyoe.verify(scope,ObjKindReferenceTree(name="U",verprot=2),force=force)

		return exptyoe
	@debugdebug
	def arginternal(self,scope,t,carry,force=True):
		ErrorObject.takeblame(self)
		if len(self.args) != t.args.lenavail(): ErrorObject.fatal("Wrong argument count.")
		fas = []
		jou = t.args.availvariables()
		for j in range(len(self.args)):
			mogol = self.args.subs[j]
			marj = jou[j].args.lenavail()

			if len(self.args.subs[j].si) != marj:
				if self.forgiveLvlup and len(self.args.subs[j].si) < marj:
					mogol = ScopeIntroducer(self.args.subs[j].si.data+[None for n in range(marj-len(self.args.subs[j].si))])
				else:
					ErrorObject.fatal("Wrong number of introduced parameters. expected "+str(marj)+", got "+str(len(self.args.subs[j].si)),self.args.subs[j].obj)
			fas.append(mogol)
		fas = SubsObject(fas) if self.forgiveLvlup else self.args
		snot = fas.postcompact(scope,t.args)
		ErrorObject.takeblame(self)
		if carry != None:
			null,nreu = RenamerObject(scope).integrate(t.args.variables.introducer())
			exptyoe = t.type.substitute(nreu,SubsObject(snot.unwrapsubs(null)))
			# exptyoe = exptyoe.verify(scope,ObjKindReferenceTree(name="U",verprot=2),force=force)
			# def recurstep(exptyoe):
			# 	valids = 0
			# 	if exptyoe.equate(CrossNameObject(),carry,force=force):
			# 		valids += 1
			# 	elif type(exptyoe) is ObjKindTypeUnion:
			# 		for j in exptyoe.subs.variables.data:
			# 			if j.args.lenavail() == 0:
			# 				valids += recurstep(j.type)
			# 	return valids
			# valids = recurstep(exptyoe)
			# ErrorObject.takeblame(self)
			# if valids > 1:
			# 	ErrorObject.nonfatal("unable to infer which member to extract from composite type")
			# if valids == 0:
			if not exptyoe.equate(CrossNameObject(),carry,force=force):
				# print("NONFATAL:   "+str(exptyoe)+" =/= "+str(carry))
				ErrorObject.nonfatal(str(exptyoe)+" =/= "+str(carry))
		return snot
	@debugdebug
	def substitute(self,revf,repl):
		yobi = self.args.substitute(revf,repl)
		if self.src != None:
			return ObjKindReferenceTree(args=yobi,src=self.src.substitute(revf,repl),name=self.name,pos=self,verprot=self.verprot)
		i = repl.get(revf[self.name])
		if i == None:
			return ObjKindReferenceTree(args=yobi,name=revf[self.name],pos=self,verprot=self.verprot)
		if type(i) is EmptyWildcardSub:
			return ObjKindWildcard()
		if type(i) is DowngradeSub:
			for j in range(len(i.cap.subs)):
				if not i.cap.subs[j].equate(CrossNameObject(),self.args.subs[j]):
					ErrorObject.takeblame(self)
					ErrorObject.fatal("Only simple references are allowed to this variable in this context.")
			return ObjKindReferenceTree(args=SubsObject(yobi.subs[len(i.cap.subs):],exverified=True),name=self.name,pos=self,verprot=self.verprot)

		tsi,ghn = RenamerObject(revf.s).integrate(i.si)


		gam = i.obj.substitute(ghn,SubsObject(yobi.triangulate(ghn.s).unwrapsubs(tsi,onlyavailable=True)))
		if type(gam) is ObjKindUnionSet:
			if gam.verprot == 0:
				gam = copy.copy(gam)
				gam.verified = False
				gam.verprot = None
		if not self.verified:
			gam.verified = False
		return gam
	def render(self,scope,carry):
		# assert self.verified#safemode
		# assert self.src==None#safemode

		wak = self.args.render(scope)
		return Statement(args=[i[1] for i in wak],name=self.name,lvlup=[i[0] for i in wak])

	@debugdebug
	def equate(self,cno,other,force=False):
		if type(other) is ObjKindWildcard: return other.equate(cno.flip(),self,force=force)
		if type(other) is not ObjKindReferenceTree: return False
		if not cno.equivalen(self.name,other.name): return False
		if not self.args.equate(cno,other.args,force=force): return False
		if self.src == None and other.src == None: return True
		if self.src == None or other.src == None: return False
		return self.src.equate(cno,other.src,force=force)
	def refs(self,label):
		if self.src == None and self.name == label: return True
		l = self.args.refs(label)
		if l: return l
		if self.src != None: return self.src.refs(label)


class ObjKindUnionSet(ObjKind):
	def __init__(self,subs=None,pos=None,verprot=None):
		self.subs = SubsObject() if subs == None else subs if type(subs) is SubsObject else SubsObject(subs)
		transferlines(self,pos)

		# self.original = original

		if   verprot == None:
			self.verified = False
		elif verprot == 0:
			self.verified = True
		elif verprot == 1:
			self.verified = self.subs.verified
		# else: assert False#safemode
		self.verprot = verprot if self.verified else None
		# if self.verified: assert self.original != None
	def __repr__(self):
		return "("+str(self.subs)+")"
	def wide_repr(self,depth):
		return "("+self.subs.wide_repr(depth+1)+"\n"+"\t"*depth+")"
	@debugdebug
	def verify(self,scope,carry,force=True):
		ErrorObject.takeblame(self)
		if self.verprot == 0 and carry == None or self.verprot == 1: return self
		if carry == None:
			ewgross = copy.copy(self)
			ewgross.verified = True
			ewgross.verprot = 0
			return ewgross

		if type(carry) is not ObjKindTypeUnion:
			ErrorObject.fatal("Can't pair keyword arguments to static type.")

		return ObjKindUnionSet(subs=self.subs.postcompact(scope,carry.subs),pos=self,verprot=1)
	@debugdebug
	def substitute(self,revf,repl):
		return ObjKindUnionSet(subs=self.subs.substitute(revf,repl),pos=self,verprot=self.verprot)
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry):
		union
	def get(self,lab):
		# assert self.verified#safemode
		return self.subs.get(lab)

	@debugdebug
	def equate(self,cno,other,force=False):
		if type(other) is ObjKindWildcard: return other.equate(cno.flip(),self,force=force)
		if type(other) is not ObjKindUnionSet: return False
		return self.subs.equate(cno,other.subs,force=force)



class ObjKindTypeUnion(ObjKind):
	def __init__(self,parsed=None,subs=None,variables=None,pos=None,exverified=False):
		transferlines(self,pos)
		if type(subs) is DualSubs:
			# assert variables == None#safemode
			self.subs = subs
		else:
			self.subs = DualSubs(variables=variables,subs=subs,exverified=exverified)
		self.verified = exverified and self.subs.verified
	def __repr__(self):
		return "{"+str(self.subs)+"}"
	def wide_repr(self,depth):
		return "{"+self.subs.wide_repr(depth+1)+"\n"+"\t"*depth+"}"
	@debugdebug
	def verify(self,scope,carry,force=True):
		ErrorObject.takeblame(self)
		if carry!=None and not(type(carry) is ObjKindReferenceTree and carry.src == None and len(carry.args) == 0 and carry.name == "U"): ErrorObject.nonfatal("U =/= "+str(carry))
		if self.verified: return self
		return ObjKindTypeUnion(subs=self.subs.verify(scope,force=force),pos=self,exverified=True)
	@debugdebug
	def compactify(self,scope,subs,needscomplete=False,force=True):
		return ObjKindTypeUnion(subs=self.subs.compactify(scope,subs,needscomplete=needscomplete,force=force),pos=self,exverified=True)
	@debugdebug
	def substitute(self,revf,subs):
		return ObjKindTypeUnion(subs=self.subs.substitute(revf,subs),pos=self,exverified=self.verified)
	def refs(self,label):
		return self.subs.refs(label)
	def render(self,scope,carry):
		oafdjosidfjoasidf

	def get(self,lab):
		return self.subs.get(lab)
	def gentype(self,scope,force=True):
		return ObjKindReferenceTree(name="U",verprot=2)

	@debugdebug
	def equate(self,cno,other,force=False):
		if type(other) is ObjKindWildcard: return other.equate(cno.flip(),self,force=force)
		if type(other) is not ObjKindTypeUnion: return False
		return self.subs.equate(cno,other.subs,force=force)




