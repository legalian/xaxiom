


	# def preverify(self,OIP):
	# 	allowed references only builds


	# 	if OIP!=None and <><><><><><><>><><><><>><<>><><><><><><>

	# 	btc = Set()
	# 	for a in range(len(self.rows)):
	# 		# if row.name == "*****": raise PreverifyError()
	# 		# if a out of range: process all remaining z
	# 		mtc = Set()
	# 		if type(row.type) is Strategy and row.type.type == None:
	# 			moum = row.type.args.preverify(OIP)
	# 			mtc.update(moum[0])
	# 			if row.obj!=None: mtc.update(row.obj.preverify(moum[1])[0])
	# 		else:
	# 			if row.type!=None: mtc.update(row.type.preverify(OIP)[0])
	# 			if row.obj!=None: mtc.update(row.obj.preverify(OIP)[0])

	# 		if (row.obj==None or row.obj.PJID != None) and (row.type==None or row.type.PJID != None):
	# 			oooooooo

	# 			iterate through new rows-> gather up illegal; offset...





	# 			offset,illegal,precompute = OIP
	# 			if any(a in mtc for a in illegal): return (mtc,None)<><>
	# 			row = row.primToJSON()<--- search onwards for match.



	# 			wild = precompute.wildin.get()
	# 			if wild == None: return (mtc,None)




	# 		row.PJID = wild[0]
	# 		return (mtc,wild[1])
	# 	self.PJID = None
	# 	mtc = Set()
	# 	for row in self.rows:
	# 		if row.name == "*****": raise PreverifyError()#call preverify upon resolution.
	# 		moum = row.preverify(offset,illegal,precompute)
	# 		mtc.update(moum[0])
	# 		if moum[1]==None:
	# 			asdfjk;lasdfjkl;asdfjkl;asjdfkl;ajsdkfl;asdfjkl;asdfjkl;

	# 		else:
	# 			precompute = moum[1]

	# 	for row in self.rows:
	# 		if row.PJID == None:
	# 			return (mtc,precompute)
	# 	wild = precompute.wildin.get(self.primToJSON())
	# 	if wild == None: return (mtc,precompute)
	# 	self.PJID = wild[0]
	# 	return (mtc,precompute)



def translateBackwardPreserve(fug,pushes):
	track = []
	for amt,lim in reversed(pushes):
		if fug>lim:
			track.insert(0,(amt,lim))
			fug-=amt
			assert fug>=lim
	return track


	def pmultiline(self,context,out,indent,prepend,postpend,callback=None):
		assert False
		# remapflat = [k.nonsilent() for k in self.flat]
		# for row in range(len(remapflat)):
		# 	cr=row
		# 	for j in self.postpushes:
		# 		if cr>=j[1]-j[0]:cr+=j[0]
		# 		elif cr>=j[1]:
		# 			cr=None
		# 			break
		# 	pr=row
		# 	for j in reversed(self.prepushes):
		# 		if pr>=j[1]+j[0]:pr-=j[0]
		# 		elif pr>=j[1]:
		# 			pr=None
		# 			break
		# 	name = "("+remapflat[row].name+")" if remapflat[row].name != None else ""
		# 	remapflat[row].name = ("" if pr == None else str(pr))+"->"+("" if cr == None else str(cr))+name
		# pmultilinecsv(context,out,indent,remapflat,prepend+"[[","]]"+postpend+repr(self.postpushes)+" -- "+repr(self.prepushes),callback=callback)


def conditionalverify(F):
	return F
	def wrapper(self,indesc,carry=None,reqtype=False,then=False,exob=None,**kwargs):
		def _dbgEnter():
			if exob!=None: exob.setSafety(len(indesc))
		"""dbg_ignore"""
		if not self.verified or (exob!=None and type(self) is not RefTree) or reqtype or then or any(len(indesc.flat) and indesc.flat[indesc.prepushes.translate(i)].hasobj() for i in self.touches):
			return F(self,indesc,carry,reqtype,then,exob,**kwargs)


		if not indesc.prepushes.isempty() or not indesc.postpushes.isempty():
			self = self.dpush(indesc.prepushes+indesc.postpushes)

		if exob!=None:
			self = RefTree(self.name,SubsObject(self.args.subs+exob.subs,verdepth=self.verdepth),self.src,verdepth=self.verdepth,pos=self,cold=self.cold).addalts(self.verifyalt(indesc,carry,exob))

		return self
		# return self
	return wrapper















	# pjson  -> touches,PJID
	# (PJID) -> [verified]


	# pJSONout -> (adds to jain and returns int? nah)


	# - before verifying, recursively assign PJIDs for anything with a match.

	# - verifying an unverified structure twice kills the program
	# - verifying an unverified structure that has a PJID already will search jain for a match to skip some computation.
	# - verifying an unverified structure assigns it a PJID in jainprime

	# ->>>>>>>>> verifying a file reference should also compare an md5 to make sure it didnt change.


	# - from json should also accept a DPUSH variable-> always applies to all.




	# def softdetect(self,ranges):
	# 	return self.type.softdetect(ranges) or self.obj!=None and self.obj.softdetect(ranges)


	# def lambdaalt(self,args,si=None):
	# 	vers = []
	# 	for ver in self.altversion:
	# 		try: vers.append(ver.addlambdas(args,si))
	# 		except DpushError: vers = vers + ver.lambdaalt(args,si)
	# 	return vers





# each time you construct a Tobj...




	# alternates are always sorted by root index
	#when comparing, alternates compare only to alternates and following sorted order, and if that fails, the object itself is compared separately.

	# verify should preserve alternates. (and set verified flag)

	# compare should use alternates.


	# maintain alternates under verify and dpush and etc etc. (ddpush?)

#lazyeval should work without alternates.



# could probably use comparison decorator for alternates.






	# def getCreativeLabel(self,amt):
	# 	mlab = 0
	# 	for g in self.flat:
	# 		if g.name=="_" and mlab==0: mlab=1
	# 		if len(g)>=3 and g.startswith("_") and g.endswith("_") and g[1:-1].isnumeric():
	# 			mlab = max(mlab,int(g[1:-1])+1)
	# 	return ["_" if mlab==0 and amt==1 else "_"+(mlab+a)+"_" for a in range(amt)]


# class Computation:
# 	def __init__(self,wildin=None,spaces=None,verjson=None):
# 		self.wildin   = {} if wildin == None else wildin
# 		self.spaces   = {} if spaces == None else spaces
# 		self.jsonobjs = [] if verjson == None else verjson
# 	def registerAndExtract(self,add,ver):
# 		self.wildin[add] = len(self.jsonobjs)
# 		space = {}
# 		self.spaces[len(self.jsonobjs)] = space
# 		self.jsonobjs.append(ver.toJSON())
# 		return Computation(self,space,self.spaces,self.jsonobjs)
# 	def register(self,add,ver):
# 		self.wildin[add] = len(self.jsonobjs)
# 		self.jsonobjs.append(ver.toJSON())
# 	def toJSON(self):
# 		return {
# 			"unverstructures":[{"k":list(k),"v":v} for k,v in self.wildin.items()]
# 			"spaces":[{"k":k,"v":[{"k":list(k),"v":v} for k,v in p.items()]} for k,p in self.spaces.items()],
# 			"verstructures":self.jsonobjs
# 		}



# class JSONComputationTransformer:
# 	def main(self,json):
# 		return Computation(
# 			{tuple(a["k"]):a["v"] for a in json["unverstructures"]},
# 			{a["k"]:{tuple(b["k"]):b["v"] for b in a["v"]} for a in json["spaces"]},
# 			json["verstructures"]
# 		)

# (indesc,rowtype,othertype,obj,blame=yoks[k][1],soften=earlyabort,extract=yoks,thot=thot,odsc=lencom1)





































