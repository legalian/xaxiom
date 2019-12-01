


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

