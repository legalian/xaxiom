
from lark import Transformer, v_args, Tree






def parsesubsfromsrc(parsed):
	if parsed.data == 'objargumentseries':
		jarf = []
		for k in range(len(parsed.children)):
			if len(parsed.children[k].children)>1:
				jarf.append(IndividualSub(None,ScopeIntroducer(parsed.children[k].children[0]),parsed.children[k].children[1]))
			else:
				jarf.append(IndividualSub(None,ScopeIntroducer([]),parsed.children[k].children[0]))
		return SubsObject(jarf)
	if parsed.data == 'objargumentnamedseries':
		ij = []
		runnin = []
		for n in range(len(parsed.children)):
			m = parsed.children[n]
			if m.data == 'objargumentplaceholder':
				nname = m.children[0 if len(m.children)==1 else 1]
				if len(m.children)>1:
					nsi = ScopeIntroducer(m.children[0])
				else:
					nsi = ScopeIntroducer([])
				ij.append(PlaceholderSub(nname,nsi))
			else:
				moch = m.children[0 if len(m.children)==1 else 1]
				nname = m.children[0] if len(m.children)==2 else None
				nobj = moch.children[-1]
				if len(moch.children)>1:
					nsi = ScopeIntroducer(moch.children[0])
				else:
					nsi = ScopeIntroducer([])

				# assert len(runnin) == len(ij)
				ij.append(IndividualSub(nname,nsi,nobj,bon = copy.copy(runnin)))
			runnin.append(nname)

		# print(ij)
		return SubsObject(ij)
	if parsed.data == 'objargumentstratseries':
		variables = [gh.children[0] for gh in parsed.children]
		argh = []
		for n in range(len(variables)):
			if len(parsed.children[n].children)==2:



				slamsubs = DownBonObject([type(g) is PlaceholderSub for g in variables[n].args.subs.subs],variables[n].args.variables.introducer())

				# slamsubs = ScopeIntroducer([k.name if type(k) is IndividualSub else None for k in variables[n].args.subs.subs])

				argh.append(IndividualSub(variables[n].name,slamsubs.jsi(),parsed.children[n].children[1],bon=[k.name for k in variables[:n]],downbon=slamsubs))
			else:
				argh.append(PlaceholderSub(variables[n].name))
		return DualSubs(StratSeries(variables),subs=SubsObject(argh))
	assert False




@v_args(meta=True)
class MyTransformer(Transformer):
	def __init__(self,wildcardlist):
		self.wclist = wildcardlist
	def objstrategy(self,parsed,meta):
		mna = None
		args = None
		sl = 0
		if isinstance(parsed[sl],str) or isinstance(parsed[sl],list):
			mna = parsed[sl]
			sl += 1
		if isinstance(parsed[sl],Tree) and parsed[sl].data == 'objargumentstratseries':
			args = parsesubsfromsrc(parsed[sl])
			sl += 1
		return ObjStrategy(pos=meta,args=args,name=mna,ty=parsed[-1])
	def treeref(self,children,meta):
		src = None
		if issubclass(type(children[0]),ObjKind):
			src = children[0]
			name = children[1]
		else:
			name = children[0]
		subs = None
		args = SubsObject([])
		for u in children:
			if hasattr(u,'data') and u.data == 'objargumentseries':
				args = parsesubsfromsrc(u)
			if hasattr(u,'data') and u.data == 'objargumentnamedseries':
				subs = parsesubsfromsrc(u)
		if subs == None:
			return ObjKindReferenceTree(src=src,name=name,args=args,pos=meta)
		return ObjKindTemplateHolder(src=ObjKindReferenceTree(src=src,name=name,args=args,pos=meta),subs=subs)
		
	def union(self,children,meta):
		jar = parsesubsfromsrc(children[0])
		if len(jar.subs) == 1:
			if len(jar.subs[0].si.dat) == 0 and jar.subs[0].name == None:
				return jar.subs[0].obj
		return ObjKindUnionSet(subs=jar,pos=meta)
	def andtype(self,parsed,meta):

		return ObjKindTypeUnion(subs=parsesubsfromsrc(parsed[0]) ,pos=meta)


	def object(self,children,meta):
		assert False
	def objectun(self,children,meta):
		return ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindTypeUnion(pos=meta,variables=[ObjStrategy(pos=meta,ty=ObjKindReferenceTree(pos=meta,name="NOT",args=[a])) for a in children])])
	def objectinter(self,children,meta):
		return ObjKindTypeUnion(pos=meta,variables=[ObjStrategy(pos=meta,ty=a,name=a.name.lower() if a.name != None and a.name[0].isupper() else None) for a in children])


	def lognot(self,children,meta):
		return ObjKindReferenceTree(pos=meta,name="NOT",args=[children[0]])

	def objectsneaky(self,children,meta):
		j = WildCardInternalObject(meta)
		self.wclist.append(j)
		assert len(children) == 0
		return ObjKindWildcard(pos=meta,unobject=j)


	def compchain(self,children,meta):
		svart = []
		g=0
		while g < len(children)-1:
			sym = str(children[g+1].data)
			if   sym == "ltsym":   start = ObjKindReferenceTree(pos=meta,name="GT",args=[children[g+2],children[g+0]])
			elif sym == "lteqsym": start = ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindReferenceTree(pos=meta,name="GT",args=[children[g+0],children[g+2]])])
			elif sym == "eqsym":   start = ObjKindReferenceTree(pos=meta,name="EQ",args=[ObjKindReferenceTree(pos=meta,name="AFF"),children[2],children[0]])
			elif sym == "neqsym":  start = ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindReferenceTree(pos=meta,name="EQ",args=[ObjKindReferenceTree(pos=meta,name="AFF"),children[2],children[0]])])
			elif sym == "gteqsym": start = ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindReferenceTree(pos=meta,name="GT",args=[children[g+2],children[g+0]])])
			elif sym == "gtsym":   start = ObjKindReferenceTree(pos=meta,name="GT",args=[children[g+0],children[g+2]])
			else: 
				print(sym)
				assert False
			svart.append(start)
			g = g + 2

		assert len(svart) > 0
		if len(svart) == 1: return svart[0]
		return ObjKindTypeUnion(pos=meta,variables=[ObjStrategy(pos=meta,ty=svar) for svar in svart])

	def scopemop(self,children,meta):
		return children


	def objectsum(self,children,meta):
		sumo = []
		nexneg = False
		for z in children:
			if   str(z) == "-": nexneg = True
			elif str(z) == "+": nexneg = False
			elif nexneg: sumo.append(ObjKindReferenceTree(pos=meta,name="AINVERSE",args=[z]))
			else: sumo.append(z)
		a = sumo[0]
		for b in sumo[1:]: a = ObjKindReferenceTree(pos=meta,name="ADD",args=[a,b])
		return a
	def objectprod(self,children,meta):
		a = children[0]
		for b in children[1:]: a = ObjKindReferenceTree(pos=meta,name="MULTIPLY",args=[a,b])
		return a
	# def sub(self,children,meta):
	# 	return ObjKindReferenceTree(pos=tree,name="ADD",args=[tree.children[0],ObjKindReferenceTree(pos=tree,name="AINVERSE",args=[tree.children[1]])])
	# def prod(self,children,meta):
	# 	return ObjKindReferenceTree(pos=tree,name="MULT",args=[tree.children[0],tree.children[1]])
	def customeq(self,children,meta):
		return ObjKindReferenceTree(pos=meta,name="EQ",args=[children[1],children[0],children[2]])
	def customneq(self,children,meta):
		return ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindReferenceTree(pos=meta,name="EQ",args=[children[1],children[0],children[2]])])

	def label(self,children,meta):
		# print(tree)
		# return str(tree)
		# return tree
		return str(children[0])


	def statement(self,children,meta):
		# print(tree,"opopop")
		# print(the,"opopop")
		return Statement(pos=meta,parsed=children)
	def strategy(self,children,meta):
		assert False#implement this later
		# if len(parsed)>1 and isinstance(parsed[-2],str):
		# 	return Strategy(pos=meta,args=StratSeries([arg for arg in parsed[0:-2]]),name=parsed[-2],ty=parsed[-1])
		# else:
		# 	return Strategy(pos=meta,args=StratSeries([arg for arg in parsed[0:-1]]),ty=parsed[-1])
	def multistrat(self,children,meta):
		return multistrat(children)











