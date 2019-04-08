
from .structures import *



class ObjKind:pass


def mapping(subsf,subso):
	construct = [None for n in subso]
	sht1 = 0
	sht2 = 0
	k=0
	for aj in range(len(subsf)):
		if subsf[aj][0] == None:
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
				return (0,k)
	for aj in range(len(subsf)):
		if subsf[aj][0] != None:
			found = False
			for ja in range(sht2,len(subso)):
				if subso[ja].name == subsf[aj][0]:
					sht1 = ja
					construct[ja] = aj
					found = True
					break
			if not found:
				for ja in range(sht2):
					if subso[ja].name == subsf[aj][0]:
						return (1,subsf[aj][0],ja)
				return (2,subsf[aj][0])
	return construct
def fillsubs(subs,carry,errors,onlycomplete,blame):
	if type(carry) is not ObjKindTypeUnion:
		errors.append((blame,"Can't pair keyword arguments to static type."))
		return
	# carry = carry.compactify(scope,errors)
	# if carry == None: return
	if carry.subs != []: return
	gar = mapping(subs,carry.variables)
	if type(gar) is tuple:
		if   gar[0] == 0: errors.append((blame,"Too many positional arguments."))#too many positional arguments
		elif gar[0] == 1: errors.append((blame,"Parameter specified twice:"+gar[1]))#parameter specified twice: positional and named
		elif gar[0] == 2: errors.append((blame,"Unrecognized named parameter:"+gar[1]))# name parameter
		else: assert False
		return
	srar = []
	for z in range(len(gar)):
		if gar[z] == None:
			if not onlycomplete: continue
			if carry.variables[z].name == None: errors.append((blame,"Not enough positional arguments."))#not enough positional arguments
			else: errors.append((blame,"Missing named argument:"+carry.variables[z].name))#missing positional argument
			return
		if len(carry.variables[z].args) != len(subs[gar[z]][1]):
			errors.append((subs[gar[z]][2],"Wrong number of introduced arguments."))#wrong number of introduced arguments.
			return
		# srar.append((carry.variables[z],subs[gar[z]][0],[subs[gar[z]][1][g] for g in range(len(carry.variables[z].args))],subs[gar[z]][2]))
		srar.append((carry.variables[z],carry.variables[z].name,subs[gar[z]][1],subs[gar[z]][2]))



	snar = [i[0] for i in srar]
	asgo = []
	foe = []
	semfoe = []
	for v in carry.variables:
		zong = v.substitute([z for z in srar if z[0] in asgo],errors,blame)
		if zong == None: return
		if v.name not in snar: foe.append(zong)
		else: asgo.append(v.name)
		semfoe.append(zong)

	return (srar,foe)


def scopemake(lvluprow,grinz,errors,blame):
	if len(lvluprow) != len(grinz):
		errors.append((blame,"Wrong number of introduced parameters."))
		return
	resk = []
	for f in range(len(lvluprow)):
		if isinstance(lvluprow[f],list):
			if type(grinz[f].type) is not ObjKindTypeUnion:
				errors.append((blame,"Tuple unwrapping only supported on union types."))
				return
			if len(grinz[f].args) != 0:
				errors.append((blame,"Function-to-tuple unwrapping is not supported."))
				return
			if len(grinz[f].type.variables) != len(lvluprow[f]):
				errors.append((blame,"Tuple unwrapping has wrong length."))
				return
			resk = resk + scopemake(lvluprow[f],grinz[f].type.variables,errors,blame)
		else:
			snot = copy.copy(grinz[f])
			snot.name = lvluprow[f]
			resk.append(snot)
	return resk



def subsmake(lvluprow,levelsup,args,errors,blame):#levelsup must be empty where lvluprow is an array...
	if len(lvluprow) != len(levelsup):
		errors.append((blame,"Wrong number of introduced parameters."))
		return
	resk = []
	for f in range(len(lvluprow)):
		if isinstance(lvluprow[f],list):
			if type(args[f]) is not ObjKindUnionSet:
				errors.append((blame,"Mechanical error: non-unionset unwrapped in given paramter for eval."))
				return
			if len(levelsup[f].args) != 0:
				errors.append((blame,"Mechanical error: Function-to-tuple unwrapping is not supported."))
				return
			if len(args[f].subs) != len(lvluprow[f]):
				errors.append((blame,"Mechanical error: Tuple unwrapping has wrong length."))
				return
			resk = resk + subsmake(lvluprow[f],[z[1] for z in grinz[f].type.subs],[z[2] for z in grinz[f].type.subs],errors,blame)
		else:
			resk.append((lvluprow[f],levelsup[f],args[f]))
	return resk




def ismember(name,lvluprow):
	for h in lvluprow:
		if h == name: return True
		if isinstance(h,list) and ismember(name,h): return True
	return False




class ObjKindTemplateHolder(ObjKind):
	def __init__(self,src=None,subs=[]):
		assert src != None
		self.src = src
		self.subs = copy.copy(subs)
		pass
	def verify(self,scope,carry,errors):
		if self.subs == []: return src

		if type(self.src) is ObjKindTypeUnion:
			if self.src.subs != []: return
			juju = fillsubs(self.subs,src,errors,False,src)

			if juju == None: return
			src = self.src.compactify(scope,juju[0],errors,blame)
			if src == None: return

			return src

		errors.append((blame,"Substitution is only supported on unions."))#substitution is unsupported
		return
	def get(self,name,args,errors,blame):
		return ObjKindTemplateHolder()
	def substitute(self,repl,errors,blame):
		return ObjKindTemplateHolder()





class ObjKindReferenceTree(ObjKind):
	def __init__(self,lvlup=None,args=[],subs=[],src=None,parsed=None,upcast=None,name=None,pos=None):
		for z in args:
			assert issubclass(type(z),ObjKind)
		self.lvlup = [[] for n in args] if lvlup == None else copy.copy(lvlup)
		self.args = copy.copy(args)
		self.name = name
		self.subs = copy.copy(subs)
		self.src = src
		self.verified = False
		self.column = 0
		self.row = 0
		self.forgiveLvlup = False
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
		if parsed != None:
			assert args == []
			assert subs == []
			assert src == None
			assert upcast == None

			ff = 0
			if issubclass(type(parsed[0]),ObjKind):
				ff = 1
				self.src = parsed[0]

			self.name = parsed[ff]

			firstlab = len(parsed)
			for u in range(ff+1,len(parsed)):
				if hasattr(parsed[u],'data') and parsed[u].data == 'objargumentnamed':
					firstlab = u
					break

			self.lvlup      = [[f for f in k.children[:-1]] for k in parsed[ff+1:firstlab]]
			self.args       = [k.children[-1] for k in parsed[ff+1:firstlab]]

			for n in parsed[firstlab:]:
				if len(n.children)==1:
					self.subs.append((None,[s for s in n.children[0].children[:-1]],n.children[0].children[-1]))
				else:
					self.subs.append((n.children[0],[s for s in n.children[1].children[:-1]],n.children[1].children[-1]))
		if upcast != None:
			assert args == []
			assert subs == []
			assert src == None
			self.column = upcast.column
			self.row = upcast.row
			self.name = upcast.name
			self.lvlup = upcast.lvlup
			self.forgiveLvlup = True

			
			self.args = [ObjKindReferenceTree(upcast=i) for i in upcast.args]
	def __repr__(self):
		if self.name == None:
			if len(self.args) == 0:
				return "~anon~"
			else:
				return "~anon~("+",".join([str(k) for k in self.args])+")"
		else:
			if len(self.args) == 0:
				return self.name
			else:
				return self.name+"("+",".join([str(k) for k in self.args])+")"

	def verify(self,scope,carry,errors):
		if self.verified: return
		self.verified = True
		snarg = []
		for g in self.subs:
			if g[0] == None: continue
			if g[0] in snarg:
				errors.append((self,"Duplicate keyword arguments."))#duplicates
				return
			snarg.append(g[0])

		if self.src != None:
			self.src.verify(scope,None,errors)
			self.pullsrc(scope,errors,self)
			return

		for t in reversed(scope):
			if t.name == self.name:
				if len(self.args) != len(t.args):
					errors.append((self,"Wrong argument count."))#wrong parameter count
					return


				if len(self.args) != len(self.lvlup):
					if self.forgiveLvlup and len(self.args) > len(self.lvlup):
						self.lvlup = self.lvlup+[[] for n in range(len(upcast.args)-len(upcast.lvlup))]
					else:
						errors.append((self,"Mechanical error: lvlup count does not match arg count."))#wrong parameter count
						return

				nscope = scope
				nrepl = []
				for j in range(len(self.args)):


					if len(self.lvlup[j]) != len(t.args[j].args):
						if self.forgiveLvlup and len(self.lvlup[j]) < len(t.args[j].args):
							self.lvlup[j] = self.lvlup[j]+["$" for n in range(len(t.args[j].args)-len(self.lvlup[j]))]
						else:
							errors.append((self,"Wrong number of introduced parameters."))#wrong introduced parameters
							return


					# the above error should be taken care of.
					grin = t.args[j].substitute(nscope,nrepl,errors,self)

					if grin == None: return
					sadd = scopemake(self.lvlup[j],grin.args,errors,self)
					if sadd == None: return
					vscope = scope+sadd
					self.args[j].verify(vscope,grin,errors)
					nscope.append((grin.name,grin))
					nrepl.append((grin.name,self.lvlup[j],self.args[j]))

				self.forgiveLvlup = False
				return
		# print(scope)
		# assert False
		errors.append((self,"Referenced variable not in scope:"+self.name))#referenced variable not in scope.
		return
	def get(self,name,args,errors,blame):
		if self.src != None:
			carry = self.src.get(self.name,[(self.lvlup[i],self.args[i]) for i in range(len(self.args))],errors,blame)
			if carry == None:return
			if self.subs != []: carry = ObjKindTemplateHolder(carry,self.subs)
			
			return carry.get(name,args,errors,blame)
		else:
			carry = ObjKindReferenceTree(lvlup=[k[0] for k in args],args=[k[1] for k in args],src=self,name=name)
			carry.column = self.column
			carry.row = self.row
			return carry
	def substitute(self,repl,errors,blame):
		if self.src != None:
			carry = self.src.get(self.name,[(self.lvlup[i],self.args[i]) for i in range(len(self.args))],errors,blame)
			if carry == None:return
			if self.subs != []: carry = ObjKindTemplateHolder(carry,self.subs)

			return carry.substitute(repl,errors,blame)

		nrepl = []
		nargs = []
		for j in range(len(self.args)):
			snap = self.args[j].substitute([r for r in repl if not ismember(r[0],self.lvlup[j])],errors,self.args[j] if blame is self else blame)
			if snap == None: return
			nargs.append(snap)
			# nscope.append((grin.name,grin))
			nrepl.append((t[1].args[j].name,self.lvlup[j],   snap   ))


		for i in self.subs:
			marm = i[2].substitute([r for r in repl if not ismember(r[0],i[1])],errors,i[2] if blame is self else blame)
			if marm == None:return
			nrepl.append((i[0],i[1],marm))


		for g in repl:
			if g[0] == self.name:

				suys = subsmake(g[1],self.lvlup,nargs,errors,blame)
				if suys == None: return
				doubleback needs to do a full inspection and deep-change variables here'
				carry = g[2].substitute(suys,errors,blame)
				if carry == None: return
				if self.subs != []: carry = ObjKindTemplateHolder(carry,self.subs)
				return carry

		carry = ObjKindReferenceTree(lvlup=self.lvlup,args=nargs,name=self.name,subs=nrepl)
		carry.column = self.column
		carry.row = self.row
		return carry

	def render(self,scope,carry,errors):
		if self.src != None: return self.src.get(self.name,errors,self).render(scope,carry,errors)
		#referencing something? had better not be- substitute should scrub the whole damn mess clean.
		#no wait- there are variables.
class ObjKindUnionSet(ObjKind):
	def __init__(self,subs=[],smam=None,bonus=[],parsed=None,pos=None):
		self.subs = copy.copy(subs)
		self.outsubs = copy.copy(bonus)
		self.name = None
		self.column = 0
		self.verified = False
		self.row = 0
		self.smam = smam
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
		if parsed != None:
			assert bonus == []
			assert subs == []
			for n in parsed:
				if len(n.children)==1:
					self.subs.append((None,[s for s in n.children[0].children[:-1]],n.children[0].children[-1]))
				else:
					self.subs.append((n.children[0],[s for s in n.children[1].children[:-1]],n.children[1].children[-1]))
	def __repr__(self):
		return "("+",".join([str(k)+":"+str(v) for (k,j,v) in self.subs])+")"
		pass

	def verify(self,scope,carry,errors):
		if self.verified: return
		self.verified = True
		snarg = []
		for g in self.subs:
			if g[0] == None: continue
			if g[0] in snarg:
				errors.append((self,"Duplicate names not allowed."))#duplicates
				return
			snarg.append(g[0])

		if carry == None:
			errors.append((self,"Unable to deduce type."))#duplicates
			return

		jam = fillsubs(self.subs,scope,carry,errors,True,self)
		if jam == None: return
		self.subs = jam[0]
		self.smam = jam[1]
		self.outsubs = []



		for o in carry.outsubs:
			asgo = []
			semvari = []
			for v in self.outsubs[4]:
				zong = v.substitute(asgo,errors,v if blame is self else blame)
				if zong == None: return
				res = None
				for i in self.subs:
					if i[0] == v.name:
						res = i
				assert res != None
				asgo.append(res)
				semvari.append(zong)
			zong = o[0].substitute(asgo,errors,v if blame is self else blame)
			if zong == None: return
			# sadd = scopemake(o[2],o[0].args,errors,self)
			# if sadd == None: return
			shazam = o[3].substitute(asgo,o[3] if blame is self else blame)
			if shazam == None: return
			self.outsubs.append((zong,o[1],o[2],shazam))






		for i in range(len(self.subs)):
			sadd = scopemake(self.subs[i][1],self.smam[i].args,errors,self)
			if sadd == None: return
			nscope = scope+sadd
			self.subs[i][2].verify(nscope,self.smam[i].type,errors)
	def substitute(self,repl,errors,blame):
		assert self.smam != None
		subu = []
		assert len(self.subs) == len(self.smam)

		for i in range(len(self.subs)):
			nrepl = [(n2,j2,v2) for (n2,j2,v2) in repl if not ismember(n2,self.subs[i][1])]
			marm = self.subs[i][2].substitute(nrepl,errors,blame)
			if marm == None: return
			subu.append((self.subs[i][0],self.subs[i][1],marm))

		zar = ObjKindUnionSet(smam = self.smam,subs = subu)
		zar.column = self.column
		zar.row = self.row
		return zar
	def get(self,name,args,errors,blame):
		assert self.smam != None

		res = None
		assert len(self.smam) == len(self.subs)
		for g in range(len(self.smam)):
			assert self.smam[g].name == self.subs[g][0]
			if self.smam[g].name == name:
				res = (self.smam[g],self.subs[g][0],self.subs[g][1],self.subs[g][2])
		if res == None:
			for g in range(len(self.outsubs)):
				if self.outsubs[g][0].name == name:
					res = self.outsubs[g]
		if res == None:
			errors.append((blame,"No such static or nonstatic property exists."))#no such property
			return

		if len(args) != len(res[0].args):
			errors.append((blame,"Wrong number of arguments provided."))#wrong number of arguments provided.
			return


		# sadd = scopemake(res[2],res[0].args,errors,blame)
		# if sadd == None: return

		suys = subsmake(res[2],self.lvlup,[z[0] for z in args],[z[1] for z in args],errors,blame)
		if suys == None: return


		return res[3].substitute(self.subs+suys,errors,blame)
	def render(self,scope,carry,errors):
		assert self.smam != None

		#assemble UNION chain here...


class ObjKindTypeUnion(ObjKind):
	def __init__(self,parsed=None,variables=[],subs=[],outsubs=[],pos=None):
		self.variables = copy.copy(variables)
		self.subs = copy.copy(subs)
		self.name = None
		self.verified = False
		self.column = 0
		self.row = 0
		self.outsubs = copy.copy(outsubs)
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
		if parsed != None:
			assert variables == []
			assert subs == []
			self.variables = [gh.children[0] for gh in parsed]
			for n in range(len(self.variables)):
				if len(parsed[n].children)==2:
					if self.variables[n].name != None:
						self.subs.append((self.variables[n].name,[j.name for j in self.variables[n].args],parsed[n].children[1]))
	def __repr__(self):
		if self.subs != []: return "unsubbed!{"+",\n".join([str(k) for k in self.variables])+"}"
		return "{"+",\n".join([str(k) for k in self.variables])+"}"
		pass

	def verify(self,scope,carry,errors):
		if self.verified: return
		self.verified = True


		snarg = []
		for g in self.variables:
			if g.name == None: continue
			if g.name in snarg:
				errors.append((self,"Duplicate names not allowed."))
				return
			snarg.append(g.name)




		for j in range(len(self.variables)):
			self.variables[j].verify(scope+self.variables[:j],errors)



		jar = self.compactify(scope,self.subs,errors,self)
		if jar == None:return
		self.variables = jar.variables
		self.subs = []
		self.outsubs = jar.outsubs

	def compactify(self,scope,subs,errors,blame):
		if subs == []: return self

		for i in subs:
			for j in range(len(self.variables)):
				if i[0] == self.variables[j].name:
					res = i
			if res == None:
				errors.append((blame,"Mechanical error- bizzare..."))
				return

			sadd = scopemake(i[1],self.variables[j].args,errors,self)
			if sadd == None: return
			# marginscope = [(p.name,p) for p in o[4]]+sadd
			# print([v.name for v in shakakan],"-=-=-=-",[m.name for m in o[4]],"<=-=-=-=new-=-")
			i[2].verify(scope+self.variables[:j]+sadd,self.variables[j].type,errors)

		# snar = [i[0] for i in self.subs]

		noutsubs = []
		for o in self.outsubs:
			asgo = []
			suho = []
			for v in self.outsubs[4]:
				zong = v.substitute(asgo,errors,v if blame is self else blame)
				if zong == None: return
				res = None
				for i in subs:
					if i[0] == v.name:
						res = i
				if res == None:
					suho.append(zong)
				else:
					asgo.append(res)
			zong = o[0].substitute(asgo,errors,v if blame is self else blame)
			if zong == None: return
			# sadd = scopemake(o[2],o[0].args,errors,blame)
			# if sadd == None: return
			shazam = o[3].substitute(asgo,errors,o[3] if blame is self else blame)
			if shazam == None: return
			noutsubs.append((zong,o[1],o[2],shazam,suho))

		asgo = []
		vari = []
		for v in self.variables:
			zong = v.substitute(asgo,errors,v if blame is self else blame)
			if zong == None: return None
			res = None
			for i in subs:
				if i[0] == v.name:
					res = i
			if res == None:
				vari.append(zong)
			else:
				asgo.append(res)

				sadd = scopemake(res[1],zong.args,errors,self)
				if sadd == None: return

				noutsubs.append((zong,res[0],res[1],res[2].substitute(asgo,errors,blame),vari))


		zar = ObjKindTypeUnion(variables = vari,outsubs=noutsubs)
		zar.column = self.column
		zar.row = self.row
		return zar
	def substitute(self,repl,errors,blame):
		if self.subs != []: return

		noutsubs = []
		for o in self.outsubs:
			asgo = repl
			suho = []
			for v in o[4]:
				zong = v.substitute(asgo,errors,v if blame is self else blame)
				if zong == None: return
				suho.append(zong)
				asgo = [r for r in asgo if r[0] != v.name]

			zong = o[0].substitute(asgo,errors,v if blame is self else blame)
			if zong == None: return
			# sadd = scopemake(o[2],o[0].args,errors,blame)
			# if sadd == None: return
			shazam = o[3].substitute(asgo,errors,o[3] if blame is self else blame)
			if shazam == None: return
			noutsubs.append((zong,o[1],o[2],shazam,suho))



		vari = []
		for v in self.variables:
			zong = v.substitute(repl,errors,v if blame is self else blame)
			if zong == None: return
			vari.append(zong)
			repl = [r for r in repl if r[0] != v.name]
		for y in vari:
			if y == None: return
		zar = ObjKindTypeUnion(variables = vari,outsubs = noutsubs)
		zar.column = self.column
		zar.row = self.row
		return zar
	def get(self,name,args,errors,blame):
		if self.subs != []: return

		#verify should check variables and subs before performing compactify.


		res = None
		for g in range(len(self.outsubs)):
			if self.outsubs[g][0].name == name:
				res = self.outsubs[g]
		if res == None:
			errors.append((blame,"No such property exists or the property exists but was not defined."))#no such property
			return

		if len(args) != len(res[0].args):
			errors.append((blame,"Wrong number of arguments provided."))#wrong number of arguments provided.
			return

		# sadd = scopemake(res[2],res[0].args,errors,blame)
		# if sadd == None: return

		suys = subsmake(res[2],[z[0] for z in args],[z[1] for z in args],errors,blame)
		if suys == None: return


		return res[3].substitute(self.subs+suys,errors,blame)



	def render(self,scope,carry,errors):
		assert self.subs == []

		#assemble AND chain here...



class ObjStrategy:
	def __init__(self,args=[],parsed=None,ty=None,name=None,upcast=None,pos=None):
		self.args = copy.copy(args)
		self.name = name
		self.type = ty
		self.column = 0
		self.row = 0
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
		if parsed != None:
			assert len(args)==0
			assert ty==None
			assert name==None
			assert upcast==None
			self.type = parsed[-1]
			if len(parsed)>1 and isinstance(parsed[-2],str):
				self.name = parsed[-2]
				self.args = [arg for arg in parsed[0:-2]]
			else:
				self.args = [arg for arg in parsed[0:-1]]
		if upcast != None:
			assert len(args)==0
			assert ty==None
			assert name==None
			self.column = upcast.column
			self.row = upcast.row
			self.name = upcast.name
			self.type = ObjKindReferenceTree(upcast=upcast.type)
			self.args = [ObjStrategy(upcast=i) for i in upcast.args]


		assert issubclass(type(self.type),ObjKind)
		# print(self.args)
		for z in self.args:
			assert type(z) is ObjStrategy
	def __repr__(self):
		if len(self.args) != 0:
			if self.name != None: return "["+",".join([str(k) for k in self.args])+"]"+self.name+":"+str(self.type)
			else: return "["+",".join([str(k) for k in self.args])+"]"+str(self.type)
		else:
			if self.name != None: return self.name+":"+str(self.type)
			else: return str(self.type)

	def verify(self,scope,errors):
		for j in range(len(self.args)):
			self.args[j].verify(scope+self.args[:j],errors)
		self.type.verify(scope+self.args,ObjKindReferenceTree(name="U"),errors)
	def substitute(self,repl,errors,blame):
		# print("subbing: ",self)
		vari = []
		for v in self.args:
			zong = v.substitute(repl,errors,v if blame is self else blame)
			if zong == None:return
			vari.append(zong)
			repl = [r for r in repl if r[0] != v.name]
		semtype = self.type.substitute(repl,errors,self.type if blame is self else blame)
		if semtype == None: return
		zar = ObjStrategy(args = vari,ty=semtype,name=self.name)
		zar.column = self.column
		zar.row = self.row
		return zar

	# def incompactify(self,givens,name,errors,blame):








def metasyntaxreports(errors,window):
	errors = list(dict.fromkeys(errors))
	phantoms = []
	scope = Scope([])
	for erroro in errors:
		error = '<span style="color:pink">█'+erroro[1]+'</span>'
		pos = window.view.text_point(erroro[0].row,erroro[0].column)
		phantoms.append(sublime.Phantom(
			sublime.Region(pos,pos+4),
			error,
			sublime.LAYOUT_BELOW
		))
	return phantoms








