
import copy
from inspect import getfullargspec

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





if True:

	def pprintlist(lis):
		def ppri(sj):
			if type(sj) is not list: return str(sj)
			return "["+",".join([ppri(k) for k in sj])+"]"
		if type(lis) is not list: return str(lis)
		return "|"+",".join([ppri(k) for k in lis])+"|"

	def pprintcsv(indent,magic,lis,head,tail,callback=None,context=None):
		if len(head)<magic:
			lisrepr = [k.prepr() for k in lis]
			comb = ",".join(lisrepr)
			if len(head)+len(comb)+len(tail)<magic:
				if callback == None:
					print("\t"*indent+head+comb+tail)
				else:
					callback(head+comb+tail,context)
				return
		print("\t"*indent+head)
		for k in range(len(lis)):
			lis[k].pprint(indent+1,"","," if k<len(lis)-1 else "",magic,context=context)
		if callback == None:
			print("\t"*indent+tail)
		else:
			callback(tail,context=context)


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


	def assertstatequal(ind,pos,one,two):
		if two != None and one != None:
			if not one.compare(ind,two):
				one.pprint(0,"one->","",20)
				two.pprint(0,"two->","",20)
				assert False


	def untrim(car,mosh):
		if type(mosh) is not list: return mosh
		assert len(car) == len(mosh)
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
	def conservativeeq(a,b):
		if type(a) is list:
			if type(b) is not list: return False
			if len(a) != len(b): return False
			return all(conservativeeq(a[c],b[c]) for c in range(len(a)))
		return type(b) is not list
	def longcount(jj):
		if type(jj) is DualSubs: return sum(longcount(k.name) for k in jj.rows)
		if type(jj) is list: return sum(longcount(k) for k in jj)
		return 1
	def trimlongcount(car,jj):

		return longcount(untrim(car,jj))
	def striphuman(lim,mosh):
		if type(mosh) is not list: return (lim,lim+1)
		ysu = []
		for jk in mosh:
			nan,lim = striphuman(lim,jk)
			ysu.append(nan)
		return (ysu,lim)









fonocolls = 0
fonodepth = 0


def downdeepverify(ahjs,amt):
	if type(ahjs) is RefTree:
		ahjs.args.setSafety(amt)
	if type(ahjs) is SubsObject:
		for j in ahjs.subs: j.setSafetyrow(amt)
	if type(ahjs) is DualSubs:
		compen = 0
		for j in ahjs.rows:
			j.setSafetyrow(amt+compen)
			compen = compen + longcount(j.name)
	if type(ahjs) is Template:
		ahjs.src.setSafety(amt)
		ahjs.subs.setSafety(amt)
	if type(ahjs) is Lambda:
		if ahjs.sc != None:
			ahjs.obj.setSafety(amt+ahjs.sc)
	if type(ahjs) is Strategy:
		ahjs.args.setSafety(amt)
		ahjs.type.setSafety(amt+longcount(ahjs.args))
def updeepverify(ahjs):
	if type(ahjs) is RefTree:
		return ahjs.args.getSafety()
	if type(ahjs) is SubsObject:
		just = None
		for j in ahjs.subs:
			just = j.getSafetyrow()
			if just != None:
				downdeepverify(ahjs,just)
				return just
	if type(ahjs) is DualSubs:
		just = None
		compen = 0
		for j in ahjs.rows:
			just = j.getSafetyrow()
			if just != None:
				downdeepverify(ahjs,just)
				return just-compen
			compen = compen + longcount(j.name)
	if type(ahjs) is Template:
		a = ahjs.src.getSafety()
		if a == None: a = ahjs.subs.getSafety()
		if a != None: downdeepverify(ahjs,a)
		return a
	if type(ahjs) is Lambda:
		if ahjs.sc != None:
			just = ahjs.obj.getSafety()
			if just != None: return just-ahjs.sc
	if type(ahjs) is Strategy:
		a = ahjs.args.getSafety()
		if a == None:
			just = ahjs.type.getSafety()
			if just != None: a = just - longcount(ahjs.args)
		if a != None: downdeepverify(ahjs,a)
		return a


def unify(self):
	invert_op = getattr(self,"getSafety",None)
	if callable(invert_op):
		invert_op()


def debugdebug(F):
	# return F
	def wrapper(*args,**kwargs):
		global fonocolls
		global fonodepth
		fonocolls += 1
		if fonocolls == 50000: assert False

		try:

			fname = F.__name__

			zaru = getfullargspec(F)
			for z in range(len(zaru.args)):
				if zaru.args[z] == 'indesc':
					args[z].setSafety(0)

			for v in args:
				unify(v)
			for k,v in kwargs.items():
				unify(v)

			if fname == 'symextract':
				args[0].setSafety(0)
			if fname == 'verify':
				tobj = args[2] if len(args)>2 else kwargs.get('carry')
				if tobj != None:
					tobj.setSafety(len(args[1]))#carry is not slotted for indesc(end) in verify
				args[0].setSafety(args[1].beginlen())#self is not slotted for indesc(begin) in verify
				if kwargs.get('exob'):
					assert type(tobj) is Strategy
					assert len(kwargs.get('exob').subs) != 0
					kwargs.get('exob').setSafety(len(args[1]))#exob is not slotted for indesc(end) in verify

			if fname == 'flatten':
				tprep = args[4] if len(args)>4 else kwargs.get('prep')
				if tprep != None: tprep[0].setSafety(tprep[1])

				tobj = args[5] if len(args)>5 else kwargs.get('obj')
				if tobj != None: tobj.setSafety(len(args[1]))

				args[0].setSafety(args[1].beginlen())

			if fname == 'peelcompactify':
				assert type(args[2]) is tuple
				for j in args[2][0]:
					assert type(j) is tuple and len(j) == 3


			if fname == 'compacrecurse':
				assert type(args[1]) is list
				for j in args[1]:
					assert type(j) is tuple and len(j) == 3
				args[0].setSafety(len(args[4]))

			if fname == 'addfibration':
				args[2].setSafety(args[1])
				args[0].setSafety(args[1]+longcount(args[2]))
				
			if fname == 'compare':
				extract = args[5] if len(args)>5 else kwargs.get('extract')
				odsc = args[3] if len(args)>3 else kwargs.get('odsc')
				if extract != None:
					assert odsc != None
					for j in extract:
						j[1].setSafety(odsc)



				if type(args[0]) is SubRow or type(args[0]) is TypeRow:
					args[0].setSafetyrow(args[1])#first value of compare doesnt match dsc...
					args[2].setSafetyrow(args[1])#second value of compare doesnt match dsc...
				else:
					args[0].setSafety(args[1])#first value of compare doesnt match dsc...
					args[2].setSafety(args[1])#second value of compare doesnt match dsc...


			# if fname == 'claimlambda':
			# 	args[0].setSafety(args[1].beginlen())
			# 	args[2].setSafety(args[1].beginlen())
			# 	args[3].setSafety(len(args[1]))
			if fname == 'phase1':
				args[0].setSafety(args[1].beginlen())
			if fname == 'addlambdas':
				args[0].setSafety(args[1])
				args[2].setSafety(args[1])



			if fname == 'reroll':
				args[0].setSafety(0)
			if fname == 'addflat':
				args[0].setSafety(0)
				args[1].setSafety(len(args[0]))
			if fname == 'invisadd':
				args[0].setSafety(0)
			if fname == 'sneakinsert':
				args[0].setSafety(0)



			ahjs = F(*args,**kwargs)



			if fname == 'symextract':
				if ahjs != None:
					outp = ahjs
					if kwargs.get('reqtype'):
						outp,ty = ahjs
						ty.setSafety(len(args[0]))
					outp.setSafety(len(args[0]))

				# if args[1]=='EQ' or args[1]==1:
				# 	print("symextract called:")
				# 	for z in range(len(zaru.args)):
				# 		mope = None
				# 		if len(args)>z: mope = args[z]
				# 		elif zaru.args[z] in kwargs: mope = kwargs[zaru.args[z]]
				# 		if hasattr(mope,'pprint'):
				# 			mope.pprint(1,zaru.args[z]+" : ","",50)
				# 		else:
				# 			print("\t"+repr(zaru.args[z]),":",mope)

				# 	if hasattr(outp,'pprint'):
				# 		outp.pprint(1,"output : ","",50)
				# 	else:
				# 		print("\toutput",":",outp)




			if fname == 'emptyinst':

				limadd = args[1] + (0 if len(args)>2 or "mog" in kwargs.items() else longcount(args[0]))

				ahjs.setSafety(limadd)
			if fname == 'dpush':
				if type(args[0]) is TypeRow or type(args[0]) is SubRow:
					safe = args[0].getSafetyrow()
					ahjs.setSafetyrow(None if safe == None else safe+args[2])
				else:
					safe = args[0].getSafety()
					ahjs.setSafety(None if safe == None else safe+args[2])
			if fname == 'verify':
				tobj = args[2] if len(args)>2 else kwargs.get('carry')

				if kwargs.get('reqtype'):
					print(type(args[0]))
					outp,natype = ahjs
					natype.setSafety(len(args[1]))
				elif kwargs.get('then'):
					outp,ninds = ahjs
					ninds.setSafety(0)
				else:
					outp = ahjs

				# print("---=/=--->",kwargs.get('exob'),args[1],args[1].flat)
				# print("---===--->",type(args[0]),type(outp),args[0],outp,outp.getSafety())
				outp.setSafety(len(args[1]))
				if type(args[0]) is SubsObject:
					assert type(outp) is SubsObject
					if len(args[0].subs) != len(outp.subs):
						print(args[2])
						print(args[0])
						print(outp)
						assert False


			if fname == 'flatten':
				if kwargs.get('fillout') == None:
					# print("flatten params:",args,kwargs,args[1].flat)
					# print("flatten result:",ahjs,ahjs.flat)

					passlen = longcount(args[4][0]) if len(args)>4 else longcount(kwargs.get('prep',([],))[0])
					# print("passlen:",passlen)
					ahjs.setSafety(len(args[1])-passlen)
			if fname == 'compacrecurse':
				if ahjs != None:
					if kwargs.get('then'):
						outp,ninds = ahjs
						ninds.setSafety(0)
					else:
						outp = ahjs
					outp.setSafety(len(args[4]))
			# if fname == 'claimlambda':
			# 	ahjs.setSafety(len(args[1]))
			if fname == 'addfibration':
				ahjs.setSafety(args[1])



			if fname == 'reroll':
				ahjs.setSafety(0)
			if fname == 'addflat':
				ahjs.setSafety(0)
			if fname == 'invisadd':
				ahjs.setSafety(0)
			if fname == 'sneakinsert':
				ahjs.setSafety(0)



			unify(ahjs)

		except Exception as u:
			relevant = type(args[0]).__name__+"."+F.__name__
			print("-traceback: "+relevant+":")
			for z in range(len(zaru.args)):
				mope = None
				if len(args)>z: mope = args[z]
				elif zaru.args[z] in kwargs: mope = kwargs[zaru.args[z]]
				if hasattr(mope,'pprint'):
					mope.pprint(1,zaru.args[z]+" : ","",50)
					# print("\t",zaru.args[z],":",mope,mope.flat)
				else:
					print("\t"+repr(zaru.args[z]),":",mope)
			raise u







		return ahjs                                                 

	return wrapper









class DpushError(Exception):
	pass


class LanguageError(Exception):
	def __init__(self,pos,message):
		message = message + " " + repr(pos)
		super(LanguageError, self).__init__(message)
		self.message = message
		transferlines(self,pos)







class ScopeObject:
	def __init__(self,flat=None,prpush=None,popush=None,oprows=None):
		self.oprows    = [] if oprows == None else oprows
		self.prepushes  = [] if prpush == None else prpush
		self.postpushes = [] if popush == None else popush
		self.flat = [] if flat == None else flat
		for i in self.postpushes:
			assert i[0]<=0
	@debugdebug
	def addflat(self,newflat):
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes,self.oprows)
	@debugdebug
	def invisadd(self,newflat):
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes+[(-len(newflat.flat),len(self))],self.oprows)
	def posterase(self,amt):
		return ScopeObject(self.flat,self.prepushes,self.postpushes+[(amt-len(self),amt)],self.oprows)
	def preerase(self,amt):
		return ScopeObject(self.flat,self.prepushes+[(len(self)-amt,self.beginlen()+amt-len(self))],self.postpushes,self.oprows)
	@debugdebug
	def sneakinsert(self,nflat,fillout):
		npop = copy.copy(self.postpushes)
		cr1=fillout
		for j in range(len(npop)):
			if cr1>=npop[j][1]-npop[j][0]:cr1+=npop[j][0]
			else: npop[j] = (npop[j][0],npop[j][1]+len(nflat.flat))
		cr0=fillout
		# for j in self.prepushes:
		# 	if cr0>=j[1]:cr0+=j[0]
		return ScopeObject(self.flat[:fillout] + nflat.flat + [k.dpush(0,len(nflat.flat),cr1) for k in self.flat[fillout:]],self.prepushes+[(len(nflat.flat),cr0)],npop,self.oprows)


	def setSafety(self,safe):
		for i in range(len(self.flat)):
			cr=i
			for j in self.postpushes:
				if cr>=j[1]-j[0]:cr+=j[0]
			self.flat[i].setSafetyrow(safe+cr)
			# if type(self.flat[i].type) is RefTree and len(self.flat[i].type.args.subs) == 0 and safe == 0:
			# 	captype = self.flat[self.flat[i].type.name].type
			# 	assert type(captype) is RefTree and len(captype.args.subs) == 0 and captype.name == 0



	def trimabsolute(self,amt):
		return ScopeObject(self.flat[:-amt],self.prepushes,self.postpushes,self.oprows)
	def prepush(self,amt,lim):
		assert amt>=0
		return ScopeObject(self.flat,self.prepushes+[(amt,lim)],self.postpushes,self.oprows)
	# def postpush(self,amt):
	# 	assert amt<=0
	# 	return ScopeObject(self.flat,self.prepushes,self.postpushes+[(amt,lim)],self.oprows)
	def beginlen(self):
		return len(self.flat) - sum([l[0] for l in self.prepushes])
	def __len__(self):
		return len(self.flat) + sum([l[0] for l in self.postpushes])
	def reroll(self):
		#be careful with reroll...
		return ScopeObject(self.flat,[(-j[0],j[1]) for j in reversed(self.postpushes)],self.postpushes,self.oprows)
	
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		remapflat = [k.nonsilent() for k in self.flat]
		for row in range(len(remapflat)):
			cr=row
			for j in self.postpushes:
				if cr>=j[1]-j[0]:cr+=j[0]
				elif cr>=j[1]:
					cr=None
					break
			pr=row
			for j in reversed(self.prepushes):
				if pr>=j[1]+j[0]:pr-=j[0]
				elif pr>=j[1]:
					pr=None
					break
			name = "("+remapflat[row].name+")" if remapflat[row].name != None else ""
			remapflat[row].name = ("" if pr == None else str(pr))+"->"+("" if cr == None else str(cr))+name
		pprintcsv(indent,magic,remapflat,prepend+"[[","]]"+postpend+repr(self.postpushes)+" -- "+repr(self.prepushes),callback=callback,context=context)


	@debugdebug
	def symextract(self,name,subs,carry=None,reqtype=False,safety=None):
		for k in subs:
			assert len(k) == 2
			assert len(k[1]) == 2
		def compachelper(assign,row):
			if row == 0: return RefTree()
			cr=row
			for j in self.postpushes:
				if cr>=j[1]-j[0]:cr+=j[0]
			curr = self.flat[row].type.dpush(0,len(self)-cr,cr)

			bedoin = DualSubs()
			cuarg = DualSubs()
			indesc = self
			earlyabort=True
			wsub = subs
			limiter = 0
			while len(wsub):
				limiter += 1
				assert limiter<10

				if type(curr) is not Strategy: return None
				se = assign(wsub,curr.args)
				if se == None: return None
				shim = curr.args.peelcompactify(indesc,se[0],then=True,earlyabort=earlyabort)
				if shim == None: return None
				wsub = [(y[0],y[1].dpush(len(shim[1])-len(indesc),len(indesc)) if y[2]!=False else y[1],y[2] if type(y[2]) is bool else y[2].dpush(len(shim[1])-len(indesc),len(indesc))) for y in se[1]]
				bedoin = bedoin + curr.args
				earlyabort=False
				indesc = shim[1]
				cuarg = cuarg+shim[0]

				curr = curr.type

			oldcurr = curr

			yolcur = oldcurr.verify(indesc.reroll(),RefTree())
			curr = yolcur.addfibration(len(self),cuarg)
			assertstatequal(len(self),None,carry,curr)

			camax = len(cuarg.rows)
			while camax>0 and (cuarg.rows[camax-1].obj==None)==(bedoin.rows[camax-1].obj==None): camax -= 1
			if self.flat[row].obj != None:
				obj = self.flat[row].obj.dpush(0,len(self)-cr,cr)
			else:
				obj = RefTree(name=cr)
			if camax != 0:

				cuarg = DualSubs(cuarg.rows[:camax])
				bedoin = DualSubs(bedoin.rows[:camax])

				nocue0 = oldcurr.addfibration(len(self),bedoin)
				nocue = nocue0.dpush(0,len(indesc)-len(self),len(self))
				print(self,"\n",indesc)
				drargs = bedoin.emptyinst(len(self)).verify(indesc.reroll(),nocue.args.verify(indesc.reroll()).nonsilent())

				if self.flat[row].obj != None:
					obj = obj.verify(indesc.reroll().preerase(len(self)),nocue,exob=drargs if len(drargs.subs)>0 else None)
					obj = obj.addlambdas(len(self),cuarg)
				else:
					obj.args = drargs
					obj = obj.addlambdas(len(self),cuarg)

			if reqtype: return (obj,curr)
			return obj

		class Scontrol:
			def __init__(self,safety):
				self.safety = safety
			def __call__(self,subs,args):
				oflow = []
				snj = args.compacassign(subs,oflow,self.safety)
				self.safety = None
				return (snj,oflow)
		def momo(subs,args):
			souts = []
			for k in range(len(args)):
				if k>=len(subs):break
				if args.rows[k].obj == None:
					souts.append(([k],subs[k][1][0],subs[k][1][1]))
			return ((souts,True),subs[len(souts):])
		if len(self.flat) == 0 or name == 0: return RefTree()
		if type(name) is int:
			row = name
			for j in self.prepushes:
				if row>=j[1]:
					row += j[0]
					if row<j[1]: assert False
			return compachelper(momo,row)
		else:
			for row in reversed(range(len(self.flat))):
				if self.flat[row].name != name: continue
				spa = compachelper(Scontrol(safety),row)
				if spa == None: continue
				return spa
				if row == 0: return None


	def precidence(self,ind):
		for j in range(len(self.oprows)):
			if ind in self.oprows[j][0]:
				return (j,self.oprows[j][1]['associate'])
	def __repr__(self):
		hu = copy.copy(self.postpushes)
		y = 0
		output = []
		for x in range(len(self.flat)):
			g=0
			while g<len(hu):
				if hu[g][1] <= y:
					y += hu[g][0]
					output.append("("+str(hu[g][0])+")")
					del hu[g]
				else: g+=1
			output.append(self.flat[x].name)
			y+=1
		for g in reversed(range(len(hu))):
			if hu[g][1] >= y:
				y += hu[g][0]
				output.append("("+str(hu[g][0])+")")
				del hu[g]
		assert not len(hu)
		return repr(output)+repr(self.postpushes)+" -- "+repr(self.prepushes)




class TypeRow:
	def setSafetyrow(self,safe):
		self.type.setSafety(safe)
		if self.obj != None: self.obj.setSafety(safe)
	def getSafetyrow(self):
		res = self.type.getSafety()
		if self.obj != None:
			if res == None:
				res = self.obj.getSafety()
				self.type.setSafety(res)
			else: self.obj.setSafety(res)
		return res
	def nonsilent(self):
		return TypeRow(self.name,self.type,self.obj,{'silent':False,'contractible':False})
	def __init__(self,name,ty,obj=None,silent=False):
		# assert type(name) is str or name == None or type(name) is list#safemode
		self.name = name
		self.type = ty
		self.obj  = obj
		self.silent = silent
		if type(ty) is Lambda or type(ty) is SubsObject: assert False
		assert self.type != None or self.obj != None
		assert type(self.type) is not Strategy or self.type.type != None or self.obj != None
	@debugdebug
	def dpush(self,dsc,amt,lim,repls=None):
		return TypeRow(self.name,self.type.dpush(dsc,amt,lim,repls),None if self.obj == None else self.obj.dpush(dsc,amt,lim,repls),self.silent)
	def prepr(self,context=None):
		res = "" if self.name == None else pprintlist(self.name)+":"
		if self.type != None: res = res+self.type.prepr(context=context)
		if self.obj != None: res = res+" = "+self.obj.prepr(context=context)
		return res
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			if self.obj != None:
				self.obj.pprint(indent,prepend,postpend,magic,callback=callback,context=context)
			else:
				if callback == None:
					print("\t"*indent+prepend+postpend)
				else:
					callback(prepend+postpend,context=context)
		name = "" if self.name == None else pprintlist(self.name)+":"
		self.type.pprint(indent,prepend+name," = " if self.obj != None else "",magic,calls)
	def __repr__(self):
		return self.prepr()



class SubRow:
	def setSafetyrow(self,safe):
		self.obj.setSafety(safe)
	def getSafetyrow(self):
		return self.obj.getSafety()

	def __init__(self,name,obj):
		# assert type(name) is str or name == None or type(name) is list#safemode
		self.name = name
		self.obj  = obj
	@debugdebug
	def dpush(self,dsc,amt,lim,repls=None):
		return SubRow(self.name,self.obj.dpush(dsc,amt,lim,repls))
	@debugdebug
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		return self.obj.compare(dsc,other.obj,odsc,thot,extract,lefpush,rigpush)
	def prepr(self,context=None):
		res = "" if self.name == None else pprintlist(self.name)+" = "
		res = res+self.obj.prepr(context)
		return res
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		name = "" if self.name == None else pprintlist(self.name)+" = "
		self.obj.pprint(indent,prepend+name,postpend,magic,callback,context=context)
	def __repr__(self):

		return self.prepr()



class Tobj:
	def setSafety(self,safe):
		if safe == None: return
		if hasattr(self,'foclnsafety'): assert self.foclnsafety == safe
		else:
			self.foclnsafety = safe
			downdeepverify(self,safe)
	def getSafety(self):
		if hasattr(self,'foclnsafety'): return self.foclnsafety
		else:
			safe = updeepverify(self)
			if safe != None: self.foclnsafety = safe
			return safe


	@debugdebug
	def flatten(self,indesc,mog,assistmog=None,prep=None,obj=None,trim=False,fillout=None):
		assert not trim
		if type(mog) is list: raise LanguageError(self,"invalid renamer pattern.")
		if prep == None or len(prep[0])==0:
			return ScopeObject([TypeRow(mog,self.verify(indesc),None if obj == None else obj)])
		else:
			njprep = prep[0].dpush(0,len(indesc)-longcount(prep[0])-prep[1],prep[1])
			spap = len(indesc)-longcount(njprep)
			return ScopeObject([TypeRow(mog,self.verify(indesc).addfibration(spap,njprep),None if obj == None else obj.addlambdas(spap,njprep))])
	@debugdebug
	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not int: raise LanguageError(self,"invalid renamer pattern.")
		# if prep != None: assert prep[1]==limit
		prep = SubsObject() if prep == None else prep[0].dpush(0,limit-prep[1],prep[1])

		return RefTree(name=mog,args=prep)
	def addfibration(self,dsc,args):
		if len(args) == 0: return self.dpush(0,-longcount(args),dsc)
		return Strategy(args,self,pos=self)
	def addlambdas(self,dsc,args):
		if len(args) == 0: return self.dpush(0,-longcount(args),dsc)
		return Lambda(args.semavail(),self,longcount(args),pos=self)
	def __repr__(self):
		return self.prepr()

class DualSubs(Tobj):
	def __init__(self,rows=None,pos=None):
		self.rows = rows if rows != None else []
		for sub in self.rows: assert type(sub) is TypeRow#safemode
		transferlines(self,pos)
	def prepr(self,context=None):
		return "{"+",".join([k.prepr(context) for k in self.rows])+"}"
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		pprintcsv(indent,magic,self.rows,prepend+"{","}"+postpend,callback=callback,context=context)
	def nonsilent(self):
		return DualSubs([k.nonsilent() for k in self.rows],pos=self)
	@debugdebug
	def dpush(self,dsc,amt,lim,repls=None):
		left = 0
		cu = []
		for k in range(len(self.rows)):
			cu.append(self.rows[k].dpush(dsc+left,amt,lim,repls))
			left += longcount(self.rows[k].name)
		return DualSubs(cu)
	@debugdebug
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is not DualSubs: return False
		if len(self) != len(other): return False
		if lefpush == None: lefpush = []
		if rigpush == None: rigpush = []
		lleft = 0
		rleft = 0
		lk = 0
		rk = 0
		limiter = 0
		while lk<len(self.rows) and rk<len(other.rows):
			limiter += 1
			assert limiter<10
			if self.rows[lk].obj != None:
				jl = longcount(self.rows[lk].name)
				lefpush = [(jl,lleft)] + lefpush
				lleft += jl
				lk += 1
			if other.rows[rk].obj != None:
				jr = longcount(other.rows[rk].name)
				rigpush = [(jr,rleft)] + rigpush
				rleft += jr
				rk += 1
			if self.rows[lk].obj==None and self.rows[rk].obj==None:
				if not conservativeeq(self.rows[lk].name,other.rows[rk].name): return False
				if not self.rows[lk].type.compare(dsc,other.rows[rk].type,odsc,thot,extract,lefpush,rigpush): return False
				j = longcount(self.rows[lk].name)
				dsc += j
				lleft += j
				rleft += j
				lk += 1
				rk += 1
		return True
	def unulimit(self,momin):
		tmomi = -1
		mopass = 0
		while mopass<=momin:
			tmomi += 1
			if tmomi>=len(self.rows) or self.rows[tmomi].obj == None: mopass += 1
		return tmomi
	def append(self,other):
		return DualSubs(self.rows+[other])
	def __add__(self,other):
		return DualSubs(self.rows+other.rows)
	def __len__(self):
		return len([k for k in self.rows if k.obj == None])
	def __getitem__(self, key):#must be verified first
		return [k for k in self.rows if k.obj == None][key].type
	def fulavail(self):
		return [j.name for j in self.rows]
	def semavail(self,mog=None):
		if mog == None: mog = self.fulavail()
		return [self.rows[k].type.semavail(mog[k]) if type(mog[k]) is list else mog[k] for k in range(len(self.rows)) if self.rows[k].obj == None]

	@debugdebug
	def flatten(self,indesc,mog=None,assistmog=None,prep=None,obj=None,trim=False,fillout=None):
		if trim: mog = untrim(self,mog)
		if mog == None: mog = self.fulavail()
		# pamt = None
		if assistmog == None:
			assistmog,ext = striphuman(len(indesc),mog)
			fillout = len(indesc.flat)
			# pamt = (len(indesc)-ext,len(indesc))
			# indesc = indesc.prepush(ext-len(indesc),len(indesc))#.prepush(ext-len(indesc),len(indesc))
			# indesc = indesc.postpush()
		if type(mog) is not list: return super(Tobj,self).flatten(indesc,mog,assistmog,prep,obj,fillout=fillout)
		if type(obj) is SubsObject: assert len(obj.subs) == len(self)
		if type(obj) is Lambda and type(obj.obj) is SubsObject: assert len(obj.obj.subs) == len(self)
		assert len(self.rows) == len(mog)
		# if all(type(f.name) is str for f in self.rows) and all(type(f) is str for f in mog):
		# 	return [i for i in self[j].flatten(obj.subs[j].obj,limit,mog[j],prep) for j in range(len(mog))]

		lenold = len(indesc)
		s = 0
		cu = ScopeObject()

		for n in range(len(self.rows)):
			nobj = None
			if self.rows[n].obj != None:
				nobj = self.rows[n].obj.verify(indesc)
			else:
				if obj == None: pass
				elif type(obj) is SubsObject: nobj = obj.subs[s].obj.dpush(0,len(indesc)-lenold,lenold)
				elif type(obj) is Lambda and obj.obj is SubsObject: nobj = Lambda(obj.si,obj.obj.subs[s].dpush(0,len(indesc)-lenold,lenold),obj.sc,obj.pos)
				else: nobj = RefTree(src=obj,name=s)
				s+=1

			# yield (n,indesc,self.rows[n],nobj)
			nflat = self.rows[n].type.flatten(indesc,mog[n],assistmog[n],prep,obj=nobj,fillout=fillout)
			cu.flat += nflat.flat
			indesc1 = indesc.sneakinsert(nflat,fillout)

			passprep = (prep[0].emptyinst(prep[1]),prep[1]) if prep != None else None



			# (when something is simplified to a scope, all replacements have been performed on it.)


			nobj = nobj.dpush(0,len(indesc1)-len(indesc),len(indesc)) if nobj != None else self.rows[n].type.emptyinst(len(indesc1),assistmog[n],prep=passprep)#prep is just the actual parameters that need to be prepended.

			oflat = self.rows[n].type.flatten(indesc1,self.rows[n].name,obj=nobj)
			indesc = indesc1.invisadd(oflat)

			# indesc = indesc.fillflat(fillout,nflat).addflat()

			# indesc = indesc.swapcert(fillout,nflat,oflat)
			fillout = fillout + len(nflat.flat)

		# if pamt != None: return cu.dpush(pamt[0],pamt[1])
		return cu


		# you forgot to dpush backwards afterwards...
	@debugdebug
	def emptyinst(self,limit,mog=None,prep=None):
		if mog == None: mog,limit = striphuman(limit,self.fulavail())
		if type(mog) is not list: return super(Tobj,self).emptyinst(limit,mog,prep)
		assert len(self.rows) == len(mog)
		mog = [mog[i] for i in range(len(mog)) if self.rows[i].obj == None]
		return SubsObject([SubRow(None,self[k].emptyinst(limit,mog[k],prep)) for k in range(len(self))])
	def needscarry(self):
		return False
	@debugdebug
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		assertstatequal(len(indesc),self,RefTree(),carry)
		outs = []
		for n in range(len(self.rows)):

			if self.rows[n].type == None:
				obj,nty = self.rows[n].obj.verify(indesc,reqtype=True)
			elif type(self.rows[n].type) is Strategy and self.rows[n].type.type == None:
				gnoa,ndsid = self.rows[n].type.args.verify(indesc,then=True)
				obj,nty = self.rows[n].obj.verify(ndsid,reqtype=True)
				nty = Strategy(gnoa,nty)
				obj = Lambda(gnoa.semavail(),obj,longcount(gnoa))
			else:
				nty = self.rows[n].type.verify(indesc,RefTree())
				obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None
			newname = self.rows[n].name if self.rows[n].name != "*****" else nty.fulavail()
			outs.append(TypeRow(newname,nty,obj,self.rows[n].silent))
			indesc = indesc.addflat(nty.flatten(indesc.reroll(),newname,obj=obj))
		if then: return (DualSubs(outs,pos=self),indesc)
		if reqtype: return (DualSubs(outs,pos=self),RefTree())
		return DualSubs(outs,pos=self)
	# def compactify(self,indesc,inyoks,force=False):
	# 	return self.peelcompactify(indesc,self.compacassign(inyoks),force=force)
	@debugdebug
	def peelcompactify(self,indesc,compyoks,then=False,force=False,earlyabort=True):
		sbu = compyoks[0]
		mo = (self,)
		limiter = 0
		while True:
			limiter += 1
			assert limiter<10
			ret = []
			# print(indesc,mo[0],sbu,"FAILED\n")
			mo = mo[0].compacrecurse(sbu,[],[],indesc,retries=ret,force=force or compyoks[1],then=True,earlyabort=earlyabort)
			# print(indesc,mo[0],sbu,ret,"FAILED\n")
			if mo == None: return None 
			earlyabort = False
			if len(ret) == 0:
				if then: return mo
				return mo[0]

			if [m[0] for m in sbu] == [m[0] for m in ret]: assert False
			sbu = ret
			# if len(sbu)



		#it should still work because you typecheck every pass. youll just be catching it late potentially. (on something that was already verified; wtf)
	def compacassign(self,inyoks,overflow=None,safety=None):
		prev = False
		for g in inyoks:
			if g[0] != None: prev = True
			elif prev: raise LanguageError(self,"positional argument may not follow keyword argument.")
		def firstnamed(spoken,labels,car,mot=None):
			# more prots
			mot = car.fulavail() if mot == None else mot
			for f in range(len(mot)):
				if car.rows[f].obj != None: continue
				if spoken[f] == True: continue
				if isinstance(mot[f],list):
					if spoken[f] == False: spoken[f] = [False]*len(mot[f])
					k = firstnamed(spoken[f],labels,car.rows[f].type,mot[f])
					if k: return [f] + k
				elif mot[f] == labels[0] or (labels[0] == None and not car.rows[f].silent['silent']):
					if len(labels) == 1:
						spoken[f] = True
						return [f]
					nxc = car.rows[f].type.type if type(car.rows[f].type) is Strategy else car.rows[f].type
					if spoken[f] == False: spoken[f] = [False]*len(nxc)
					k = firstnamed(spoken[f],labels[1:],nxc)
					if k: return [f]+k
		def fullp(spoken):
			if spoken == False: return False
			return spoken == True or all(fullp(k) for k in spoken)
		spoken = [False]*len(self.rows)
		yoks = []
		for s in range(len(inyoks)):
			nan = firstnamed(spoken,[None] if inyoks[s][0] == None else inyoke[s][0],self)
			if nan == None:
				if safety != None and s < safety: return None
				overflow.append(inyoks[s])
			else:
				yoks.append((nan,inyoks[s][1][0],inyoks[s][1][1]))
		return (yoks,fullp(spoken))
	@debugdebug
	def compacrecurse(self,yoks,trail,prep,indesc,retries=None,force=False,then=False,earlyabort=False):
		print("YAYEET",yoks," -=- ",indesc," -=- ",self)
		def namerical(lim,names,sof):
			if type(names) is not list: return [(lim,sof)]
			i = []
			for j in range(len(names)):
				i = i+namerical(lim+len(i),names[j],sof+[j])
			return i
		cu = []
		thot = prep
		for n in range(len(self.rows)):
			row = self.rows[n]
			rowtype = row.type.verify(indesc.reroll())
			if self.rows[n].obj != None:
				obj = self.rows[n].obj.verify(indesc.reroll()) 
			else:
				obj = None
				lentotal = len(indesc)
				lentho   = len(thot)
				lencom1  = lentotal - lentho
				for k in yoks:
					if k[0] == trail+[n]:
						print("YEYEET FOUND:",k)
						if k[2] != False:
							if k[2] != True:
								print("earlyabort:",earlyabort,indesc,indesc.flat)
								print("TYPE COMPARE:",k[2],k[2].dpush(0,lentho,lencom1),lentho,lencom1,rowtype)
								print("metas",n,thot,retries)
								if not rowtype.compare(lentotal,k[2].dpush(0,lentho,lencom1),lencom1,thot,retries):
									if earlyabort: return None
									assert False
							obj = k[1].dpush(0,lentho,lencom1)
							print("obj is :",obj)
							break
						if earlyabort:
							retries.append(k)
							break
						if type(k[1]) is Lambda and not k[1].obj.needscarry() and type(rowtype) is Strategy and len(rowtype.args) == len(k[1].si):
							try:
								yasat = rowtype.args.dpush(0,-lentho,lencom1)
							except DpushError: pass
							else:
								nobj,ntyp = k[1].obj.verify(indesc.trimabsolute(len(prep)).addflat(yasat.flatten(indesc,k[1].si,trim=True)),reqtype=True)
								if not rowtype.compare(lentotal,ntyp.dpush(0,lentho,lencom1),lentotal,thot,retries): assert False
								obj = nobj.dpush(0,lentho,lencom1)
								break
						try: rowtype.dpush(0,-lentho,lencom1)
						except DpushError:
							if not force:
								retries.append(k)
								break
						obj = k[1].verify(indesc.prepush(lentho,lencom1),rowtype)
						break
			# yield (n,indesc,self.rows[n],obj)
			if any(len(o[0])>len(trail)+1 and o[0][:len(trail)+1] == trail+[n] for o in yoks):
				moro = rowtype.compacrecurse(yoks,trail+[n],thot,indesc,retries=retries,force=force,earlyabort=earlyabort)
				if moro == None: return None
				obj = row.obj if row.obj != None else SubsObject() if moro.isemptytype() else None
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				obj = row.obj.verify(indesc.reroll()) if row.obj != None else obj if obj != None else None
				cu.append(TypeRow(row.name,rowtype,obj,self.rows[n].silent))

			thot = thot+namerical(len(indesc)+len(thot),self.rows[n].name,trail+[n])
			indesc = indesc.addflat(self.rows[n].type.flatten(indesc.reroll(),self.rows[n].name,obj=obj))

		if then: return (DualSubs(cu),indesc)
		return DualSubs(cu)

class SubsObject(Tobj):
	def __init__(self,subs=None,pos=None):
		self.subs = subs if subs != None else []
		for sub in self.subs: assert type(sub) is SubRow#safemode
		transferlines(self,pos)
	def prepr(self,context=None):
		return "("+",".join([k.prepr(context) for k in self.subs])+")"
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		pprintcsv(indent,magic,self.subs,prepend+"(",")"+postpend,callback=callback,context=context)
	@debugdebug
	def dpush(self,dsc,amt,lim,repls=None):
		return SubsObject([k.dpush(dsc,amt,lim,repls) for k in self.subs],self)
	@debugdebug
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is not SubsObject: return False
		if len(self.subs) != len(other.subs): return False
		return all(self.subs[k].compare(dsc,other.subs[k],odsc,thot,extract,lefpush,rigpush) for k in range(len(self.subs)))
	@debugdebug
	def phase1(self,indesc):
		return [(s.name,(s.obj,False)) if s.obj.needscarry() else (s.name,s.obj.verify(indesc,reqtype=True)) for s in self.subs]
	def phase1_gentle(self):
		for s in self.subs: assert s.name == None
		return [(None,(s.obj,True)) for s in self.subs]
	def needscarry(self):
		return True
	@debugdebug
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert type(carry) is DualSubs
		assert exob == None

		# print("eat cancer",carry,indesc,self.phase1(indesc))
		oflow = []
		garbo = carry.compacassign(self.phase1(indesc),overflow=oflow)
		if len(oflow):
			raise LanguageError(self,"cannot match with type: "+repr(carry)+"   "+repr(oflow))
		st = carry.peelcompactify(indesc,garbo,force=False)

		# st = carry.compactify(indesc,self.phase1(indesc)).rows
		for j in st: assert j.obj != None
		cuu = []
		left = 0
		for g in range(len(st.rows)):
			if carry.rows[g].obj == None:
				cuu.append(SubRow(None,st.rows[g].obj.dpush(0,-left,len(indesc))))
			left += longcount(carry.rows[g].name)
		assert not reqtype
		return SubsObject(cuu)

class Template(Tobj):
	def __init__(self,obj,subs,pos=None):
		assert type(subs) is SubsObject
		self.subs = subs
		self.obj = obj
		transferlines(self,pos)
	def needscarry(self):
		return False
	@debugdebug
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		# res = self.obj.verify(indesc,RefTree())
		# assert type(res) is DualSubs
		# sob = res.compactify(indesc,carry.phase1(indesc),force=True)
		# if reqtype: (sob,RefTree())
		return RefTree()
	def prepr(self,context=None):
		return self.obj.prepr(context)+"<"+",".join([k.prepr(context) for k in self.rows])+">"
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			pprintcsv(indent,magic,self.subs.subs,prepend+"<",">"+postpend,callback=callback,context=context)
		self.obj.pprint(indent,prepend,"",magic,calls)

class Lambda(Tobj):
	def __init__(self,si,obj,sc=None,pos=None):
		# assert type(si) is ScopeIntroducer or type(si) is DualSubs
		self.si = si
		self.obj = obj
		self.sc = sc
		transferlines(self,pos)
	@debugdebug
	def dpush(self,dsc,amt,lim,repls=None):
		return Lambda(self.si,self.obj.dpush(dsc+self.sc,amt,lim,repls),self.sc,pos=self)
	@debugdebug
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is not Lambda: return False
		assert self.sc == other.sc
		return conservativeeq(self.si,other.si) and self.obj.compare(dsc+self.sc,other.obj,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		if len(self.si) == 0: return self.obj.needscarry()
		return True
	@debugdebug
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		if exob != None and len(exob.subs) < len(self.si):
			return Lambda(self.si[:len(exob.subs)],Lambda(self.si[len(exob.subs):],self.obj)).verify(indesc,carry,reqtype,then,exob)

		if len(self.si) == 0: return self.obj.verify(indesc,carry,reqtype,then,exob)
		assert not reqtype
		if carry==None: raise LanguageError(self,"type of arguments could not be inferred.")
		if type(carry) is not Strategy: raise LanguageError(self,"lambda provided to non-lambda type.")
		if len(self.si) > len(carry.args): raise LanguageError(self,"too many lambda arguments provided.")
		tmomi = carry.args.unulimit(len(self.si))
		truncargs = DualSubs(carry.args.rows[:tmomi])
		ntype = carry.type.addfibration(len(indesc)+longcount(truncargs),DualSubs(carry.args.rows[tmomi:]))
		if exob == None:
			fid = self.obj.verify(indesc.addflat(truncargs.flatten(indesc.reroll(),self.si,trim=True)),ntype)
		else:
			nnex = SubsObject(exob.subs[len(self.si):]) if len(exob.subs)>len(self.si) else None
			exfla = SubsObject(exob.subs[:len(self.si)])

			beflat = truncargs.flatten(indesc.reroll(),self.si,obj=exfla,trim=True)

			# jjar = indesc.invisadd()
			# print("sanity: ",jjar,nnex,self.obj,ntype.verify(jjar))
			return self.obj.verify(indesc.invisadd(beflat),ntype.verify(indesc.reroll().invisadd(beflat)),exob=nnex)

		jsi = self.si
		if type(fid) is Lambda:
			jsi = self.si + fid.si
			tmomi = carry.args.unulimit(len(jsi))
			truncargs = DualSubs(carry.args.rows[:tmomi])
			fid = fid.obj


		untrimmed = untrim(truncargs,jsi)

		jaja,odsc = striphuman(len(indesc),untrimmed)
		allpassalong = truncargs.emptyinst(odsc,jaja)

		limiter = 0

		elim = 0
		if type(fid) is RefTree and fid.name<len(indesc):
			dsc = odsc
			while elim<len(allpassalong.subs) and elim<len(fid.args.subs):
				
				limiter += 1
				assert limiter<10

				if not fid.args.subs[len(fid.args.subs)-1-elim].compare(odsc,allpassalong.subs[len(allpassalong.subs)-1-elim]): break

				while tmomi>0:
					tmomi -= 1
					dsc -= longcount(truncargs.rows[tmomi].name)
					if truncargs.rows[tmomi].obj == None: break

				elim+=1

			if odsc != dsc:
				fid = copy.copy(fid)
				fid.args = SubsObject([k.dpush(0,dsc-odsc,odsc) for k in fid.args.subs[:len(fid.args.subs)-elim]])


		if len(jsi) == elim: return fid.dpush(0,dsc-odsc,odsc)
		return Lambda(jsi[:len(jsi)-elim],fid,longcount(truncargs),pos=self)

	def addlambdas(self,dsc,args):
		if len(args) == 0: return self
		return Lambda(self.si+args.semavail(),self.obj,None if self.sc == None else self.sc+longcount(args),pos=self)
	def prepr(self,context=None):
		return pprintlist(self.si)+self.obj.prepr(context)
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		self.obj.pprint(indent,prepend+pprintlist(self.si),postpend,magic,callback,context)

class Strategy(Tobj):
	def __init__(self,args=None,type=None,pos=None):
		self.args = DualSubs(pos=pos) if args == None else args
		self.type = type
		transferlines(self,pos)
		# assert type(self.args) is DualSubs#safemode
	@debugdebug
	def dpush(self,dsc,amt,lim,repls=None):
		return Strategy(self.args.dpush(dsc,amt,lim,repls),self.type.dpush(dsc+longcount(self.args),amt,lim,repls),self)
	@debugdebug
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is not Strategy: return False
		return self.args.compare(dsc,other.args,odsc,thot,extract,lefpush,rigpush) and self.type.compare(dsc+longcount(self.args),other.type,odsc,thot,extract,lefpush,rigpush)
	def addfibration(self,dsc,args):
		return Strategy(self.args+args,self.type,pos=self)
	def fulavail(self):
		return self.type.fulavail()
	def semavail(self,mog):
		return self.type.semavail(mog)
	@debugdebug
	def emptyinst(self,limit,mog,prep=None):
		sc = longcount(self.args)
		if prep == None: prep = (SubsObject(),limit)
		prep = prep[0].dpush(0,limit+sc-prep[1],prep[1]).subs if prep != None else []
		return Lambda(self.args.semavail(),self.type.emptyinst(limit+sc,mog,(SubsObject(prep+self.args.emptyinst(limit).subs),limit+sc)),sc=sc)
	@debugdebug
	def flatten(self,indesc,mog=None,assistmog=None,prep=None,obj=None,trim=False,fillout=None):

		ij = self.args.getSafety()

		arflat = self.args.flatten(indesc)
		print("------>",len(indesc),ij)
		if obj != None:
			print("begin->",self,self.getSafety())
			print("ddddd->",indesc)
			print("ddddd->",indesc.reroll().sneakinsert(arflat,len(indesc)))

			# self -> indesc.beginlen()
			# self needs to be in the output space, not the input space
			# verify it below, and make that longcount depth push into a postpush.(wait no... its positive so it needs to be a prepush.)

			sbs = indesc.sneakinsert(arflat,len(indesc))
			mascope = indesc.reroll().sneakinsert(arflat,len(indesc))

			#try it in the morn

			obj = obj.verify(mascope,self.verify(sbs),exob=self.args.emptyinst(len(indesc)))
		arp = self.args.verify(indesc)

		njprep = (arp,len(indesc)) if prep == None else (prep[0].dpush(0,len(indesc)-longcount(prep[0])-prep[1],prep[1])+arp,len(indesc)-longcount(prep[0]))
		return self.type.flatten(indesc.addflat(arflat),mog,assistmog,njprep,obj,trim,fillout=fillout)
	def needscarry(self):
		if len(self.args) == 0: return self.type.needscarry()
		return False
	@debugdebug
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		assert exob == None
		verargs,thendesc = self.args.verify(indesc,then=True)
		if len(verargs) == 0:
			thendesc = thendesc.posterase(len(indesc))
			return self.type.verify(thendesc,carry,reqtype=reqtype,then=then)
		assertstatequal(len(indesc),self,RefTree(),carry)
		vertype = self.type.verify(thendesc,RefTree(),then=then)
		if then: vertype,th = vertype
		if type(vertype) is Strategy:
			verargs = verargs + vertype.args
			vertype = vertype.type
		if reqtype: return (Strategy(args=verargs,type=vertype,pos=self),RefTree())
		if then: return (Strategy(args=verargs,type=vertype,pos=self),th)
		return Strategy(args=verargs,type=vertype,pos=self)
	def prepr(self,context=None):
		return "["+",".join([k.prepr(context=context) for k in self.args.rows])+"]"+(self.type.prepr(context=context) if self.type!=None else "None")
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			self.type.pprint(indent,prepend,postpend,magic,callback=callback,context=context)
		pprintcsv(indent,magic,self.args.rows,prepend+"[","]",callback=calls,context=context)

class RefTree(Tobj):
	def __init__(self,name=None,args=None,src=None,safety=None,pos=None):
		self.name   = 0 if name == None else name
		self.args   = SubsObject(pos=pos) if args == None else args
		self.src    = src
		self.safety = safety
		# if self.name == 8: assert False
		transferlines(self,pos)
	@debugdebug
	def dpush(self,dsc,amt,lim,repls=None):
		gy = self.name
		if gy >= lim and self.src == None:
			gy += amt
			if gy < lim:
				if repls == None: raise DpushError
				for j in repls:
					fom = self.dpush(dsc,lim-amt-len(repls)-dsc,lim-amt-len(repls))
					if fom == None: continue
					if fom.compare(dsc,j[0]): return j[1]
				raise DpushError

		return RefTree(gy,self.args.dpush(dsc,amt,lim,repls),None if self.src == None else self.src.dpush(dsc,amt,lim,repls),self)
	@debugdebug
	def compare(self,dsc,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is not RefTree: return False
		if self.src != None:
			if other.src == None or not self.src.compare(dsc,other.src,odsc,thot,extract,lefpush,rigpush): return False
		elif thot != None:
			for k in thot:
				if k[0] == self.name:
					# assert False
					for j in extract:
						if j[0] == k[1] and j[2] == False: return True
					# assert False
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
					# assert False
					gr = other.dpush(dsc,odsc+len(repls)-dsc,dsc,repls=repls)
					mod = gr if len(repls) == 0 else Lambda(["_"]*len(repls),gr,len(repls))
					# if len(repls) == 0: return gr
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(odsc,mod)
					# assert False
					extract.append((k[1],mod,True))
					return True
		lefname = self.name
		rigname = other.name
		if lefpush != None:
			for lef in lefpush:
				if lefname>=lef[1]: lefname+=lef[0]
		if rigpush != None:
			for rig in rigpush:
				if rigname>=rig[1]: rigname+=rig[0]
		return lefname == rigname and self.args.compare(dsc,other.args,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		return False
	@debugdebug
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		p1 = self.args.phase1(indesc)
		if exob != None: p1 = p1 + exob.phase1_gentle()

		if self.src == None:
			tra = indesc.symextract(self.name,p1,reqtype=reqtype,safety=self.safety)
			if tra != None: return tra
			assert False
		else:
			orig = src.verify(self,indesc,reqtype=True)
			if type(orig[1]) is DualSubs:
				tra = orig[1].flatten(indesc,obj=orig[0]).symextract(self.name,p1,reqtype=reqtype,safety=self.safety)
				if tra != None: return tra
			if type(orig[0]) is RefTree and orig[0].src == None:
				tra = indesc.symextract(orig[0].name+"."+self.name,orig[0].args.phase1_gentle()+p1,reqtype=reqtype,safety=self.safety)
				if tra != None: return tra
			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,safety=self.safety)
			if tra != None: return tra
			assert False
	def prepr(self,context=None):
		if type(self.name) is int and context != None and self.name<len(context):
			res = str(context[self.name])
		elif hasattr(self,'foclnsafety'):
			res = str(self.name)+"`"+str(self.foclnsafety)+"`"
		else: res = str(self.name)
		if self.src != None: res = self.src.prepr(context=context)+"."+res
		if len(self.args.subs)>0: res = res+"("+",".join([k.prepr(context=context) for k in self.args.subs])+")"
		return res
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		def calls(prepend,context=None):
			if type(self.name) is int and context != None and self.name<len(context):
				res = str(context[self.name])
			else: res = str(self.name)
			# assert context!=None

			if len(self.args.subs)==0:
				if callback == None:
					print("\t"*indent+prepend+res+postpend)
				else:
					callback(prepend+res+postpend,context=context)
			else:
				pprintcsv(indent,magic,self.args.subs,prepend+res+"(",")"+postpend,callback=callback,context=context)
		if self.src == None: calls(prepend,context=context)
		else: self.src.pprint(indent,prepend,".",magic,callback=calls,context=context)

class OperatorSet(Tobj):
	def __init__(self,array,pos):
		self.array = array
		transferlines(self,pos)
	def needscarry(self):
		return False
	@debugdebug
	def verify(self,indesc,carry=None,reqtype=False,then=False,exob=None):
		# return RefTree()
		fulltree = []
		insert = fulltree
		for ind in self.array:
			if type(ind) is str:
				if insert == None:
					(prec,nesting) = indesc.precidence(ind)
					shift = fulltree
					while len(shift[-1]) == 3 and shift[-1][1] < prec or shift[-1][1] == prec and nesting:
						shift = shift[-1][2]
					shift[-1] = (ind,prec,[shift[-1]])
					insert = shift[-1][2]
				else:
					urnary = (ind,indesc.precidence(ind)[0],[])
					insert.append(urnary)
					insert = urnary[2]
			else:
				insert.append(ind.verify(indesc,reqtype=True))
				insert = None
		def douparse(tree,exob=None):
			if len(tree) == 2: return tree
			p1 = [(None,douparse(u)) for u in tree[2]]
			if exob != None: p1 = p1+exob.phase1_gentle()
			ghi = indesc.symextract(tree[0],p1,reqtype=True,safety=len(tree[2]))
			if ghi == None: raise LanguageError(self,"operator not defined for these arguments.")
			return ghi
		if reqtype: return douparse(fulltree[0],exob=exob)
		return douparse(fulltree[0],exob=exob)[0]
	def prepr(self,context=None):
		ssa = []
		for k in self.array:
			if type(k) is str: ssa.append(k)
			elif type(k) is OperatorSet: ssa.append("("+k.prepr(context=context)+")")
			else: ssa.append(k.prepr(context=context))
		return " ".join(ssa)
	def pprint(self,indent,prepend,postpend,magic,callback=None,context=None):
		short = self.prepr(context=context)
		if len(short)+len(prepend)<=magic:
			print("\t"*indent+prepend+short+postpend)
			return
		rowprep = prepend
		for token in range(len(self.array)):
			if type(self.array[token]) is str:
				rowprep+=self.array[token]+" "
			else:
				if token == len(self.array)-1:
					self.array[token].pprint(indent,rowprep,postpend,magic,callback=callback,context=context)
				else:
					self.array[token].pprint(indent,rowprep,"",magic,callback=None,context=context)





#flatten could be one-pass, you know. it could perform the same function as verify, which would be mondo cool.
#instead of verify-flatten, just flatten



#add flavored 'then' keyword- silentadd, addflat



# game(animation editor)
# hackathon
# this

# minecraft server
# hackathon(eric)


#bring back pos system and get better error tracking.


# push some of the verification to instantiation: a.b must share the same first parameters as a .


 # have multiple channels for refferring back to a specific caller.

# [] needs safety too- [a:jfie,b:ifjei][bn] = |bn|daojsidfioa

# you feel me.

# also you forgot to automatically construct the lambdas i think...
# or notl..


#imports should import everything that matches.


#list of mangles:

#mangle 2: compact variables (tracked through attached object.)
#mangle 3: when type is Strategy<DualSubs>, wrap self in singleton to try to match it.
	#applies to symextract and lambda
	#when too many lambda arguments are provided, the remainder is wrapped in a singleton and the match is attempted.
#mangle 4: when type is equality in space of DualSubs, accept tuple of equalities.
	#mangle 5: when type is equality in space of functions, accept lambda of equalities.
#mangle 5: when type is [k:K]P and you provide P it should just assume constant.



#if the time spent inside the compare function accounts for a significant portion of the runtime, then you should implement a list of previous substitutions to compare instead
#	those ladders may be subbed out already. they vanish when dpush clobbers them.


#you need to fine-tune the operator precidence and associativity.



