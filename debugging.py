
# from inspect import getfullargspec





# class ErrorObject(BaseException):
# 	blame = None
# 	absorbing = False
# 	rer = []

# 	def takeblame(obk):

# 		ErrorObject.blame = obk
# 	def fatal(err,obk=None):
# 		ErrorObject.nonfatal(err,obk)
# 		raise ErrorObject()
# 	def nonfatal(err,obk=None):
# 		if ErrorObject.absorbing: raise ErrorObject()
# 		assert type(err) is str#safemode
# 		if obk == None:
# 			assert ErrorObject.blame != None#safemode
# 			ErrorObject.rer.append((err,ErrorObject.blame))
# 		else:
# 			ErrorObject.rer.append((err,obk))

# 	def reports(window,raw):
# 		errors = list(dict.fromkeys([(o[0],o[1].row,o[1].column) for o in ErrorObject.rer]))
# 		phantoms = []
# 		for erroro in errors:
# 			error = '<span style="color:pink">█'+erroro[0].replace('>','&gt;').replace('<','&lt;')+'</span>'
# 			pos = window.view.text_point(erroro[1],erroro[2])
# 			phantoms.append(sublime.Phantom(
# 				sublime.Region(pos,pos+4),
# 				error,
# 				sublime.LAYOUT_BELOW
# 			))

# 		for gosh in raw:
# 			if gosh.possib == None:
# 				error = '<span style="color:green">█Unable to deduce type of wildcard.</span>'
# 			else:
# 				error = '<span style="color:#bfff00">█'+str(gosh.carry).replace('>','&gt;').replace('<','&lt;')+'</span><span style="color:green">'
# 				for sin in gosh.possib.values():
# 					error = error + '<br>'
# 					if sin[1] != None:
# 						error = error + '<span style="color:#d8ec8f">'+str(sin[1]).replace('>','&gt;').replace('<','&lt;')+'</span>'
# 					error = error + sin[0].replace('>','&gt;').replace('<','&lt;')
# 				error = error+'</span>'
# 			pos = window.view.text_point(gosh.row,gosh.column)
# 			phantoms.append(sublime.Phantom(
# 				sublime.Region(pos,pos+4),
# 				error,
# 				sublime.LAYOUT_BELOW
# 			))
# 		return phantoms

# 	def __str__(self):
# 		if len(ErrorObject.rer) == 1:
# 			return str((ErrorObject.rer[0][0],ErrorObject.rer[0][1].row,ErrorObject.rer[0][1].column))
# 		return "multiple errors"
# class BadRefError(BaseException):
# 	def __init__(self,ref):
# 		super()
# 		self.ref = ref



# class DebuggerRenamerObject:
# 	def __init__(self,scope):
# 		if type(scope) is StratSeries:
# 			self.s = [k.name for k in scope.flat]
# 		else:
# 			for a in scope:
# 				assert a == None or type(a) is str
# 			self.s = scope
# 		self.data = {"foo":"bar"}
# 	def integrate(self,si):
# 		return (si,DebuggerRenamerObject(self.s+si.allvars()))
# 	def __repr__(self):
# 		return "debugging object("+",".join(self.s)+")"
# 	def __getitem__(self,key):
# 		if key != "U" and key not in self.s:
# 			raise BadRefError(key)
# 			assert False
# 			# Raise(ErrorObject)
# 		return key








# def debugdebug(F):
# 	return F
# 	def wrapper(*args,**kwargs):
# 		# global fonocolls
# 		# global fonodepth
# 		# fonocolls += 1
# 		# if fonocolls == 500000: assert False
# 		janh = F.__name__

# 		zaru = getfullargspec(F)


# 		for i in range(len(zaru[0])):
# 			if zaru[0][i] == "scope":
# 				thascope = args[i]
# 				# try:
# 				# 	args[0].substitute(DebuggerRenamerObject(args[i]),SubsObject())
# 				# 	args[i].substitute(DebuggerRenamerObject([]),SubsObject())
# 				# except BadRefError as u:
# 				# 	ErrorObject.fatal("referenced something illegal(OOV): "+u.ref)
# 				# # print("entering: ",type(args[0]).__name__+"."+janh)
# 				# # print(type(args[i]))
# 				# assert type(args[i]) is StratSeries
# 				# assert args[i].verified
# 				# RenamerObject(args[i])
# 			if zaru[0][i] == "carry":
# 				if type(args[0]) is ObjKindWildcard:
# 					print("----->>>>",args[i])
# 				# try:
# 				# 	if args[i]!=None:
# 				# 		args[i].substitute(DebuggerRenamerObject(thascope),SubsObject())
# 				# except BadRefError as u:
# 				# 	ErrorObject.fatal("referenced something illegal(OOV(C)): "+u.ref)



# 		# if janh == "bgroup":
# 		# 	try:
# 		# 		RenamerObject(args[1])
# 		# 		# if len(args)>2:
# 		# 		# 	for blah in allvars(args[2]):
# 		# 		# 		assert blah in args[1]
# 		# 		args[0].substitute(DebuggerRenamerObject(args[1]),SubsObject())
# 		# 	except BadRefError as u:
# 		# 		print("fuck",args[0],args[1],args[2])
# 		# 		ErrorObject.fatal("referenced something illegal(OOB): "+u.ref)



# 		if janh == "substitute":
# 			assert args[0].verified
# 		# 	if type(args[1]) is RenamerObject:
# 		# 		try:
# 		# 			args[0].substitute(DebuggerRenamerObject(args[1].s),SubsObject())#even this gives some leyway...
# 		# 		except BadRefError as u:
# 		# 			assert False
# 		# 			ErrorObject.fatal("referenced something illegal(OOS): "+u.ref)
# 		# 		try:
# 		# 			for h in args[2].subs:
# 		# 				if type(h) is IndividualSub:
# 		# 					h.substitute(DebuggerRenamerObject(args[1].s),SubsObject())
# 		# 		except BadRefError as u:
# 		# 			# assert False
# 		# 			ErrorObject.fatal("referenced something illegal(OOS(S)): "+u.ref)
			
# 		# 	if len(args[1].s): assert args[1].s[0] == "U"
# 		# 	for u in args[2].subs:
# 		# 		assert type(u.name) is str
# 		# 		if u.name not in args[1].s and u.name != None:
# 		# 			print("-="*10)
# 		# 			print("<><><><->:",args[1].s)
# 		# 			print("<><><><->:",args[2])
# 		# 			print("CONCERN:",u.name)
# 		# 			assert u.name in args[1].s


# 		if janh == "equate":
# 			if not (args[0].verified and args[2].verified):
# 				print("error on: ",type(args[0]).__name__+"."+janh)
# 				assert False
# 			assert args[0].verified
# 			assert args[2].verified

# 		try:
# 			# if janh != "substitute" and janh != "subsmake":
# 			# 	print("\t"*fonodepth+"entering: ",type(args[0]).__name__+"."+janh)
# 			# fonodepth += 1
# 			# fonodepth -= 1

# 			ahjs = F(*args,**kwargs)

# 			return ahjs
# 		except ErrorObject as u:
# 			if not ErrorObject.absorbing:
# 				relevant = type(args[0]).__name__+"."+F.__name__
# 				iswide = callable(getattr(args[0], "wide_repr", None))
# 				strin = args[0].wide_repr(0) if iswide else str(args[0])
# 				if janh == "substitute":
# 					print("-traceback: "+relevant+" -->",strin,args[1],args[2])
# 				elif janh == "verify":
# 					print("-traceback: "+relevant+" -->",strin,[k.name for k in args[1].flat])
# 				elif janh == "precompact":
# 					print("-traceback: "+relevant+" -->",strin,args[2].original.dat,[k.name for k in args[1].flat])

# 				else:
# 					print("-traceback: "+relevant+" -->",strin)
# 			raise u


# 		if janh == "verify":
# 			if not ahjs.verified:
# 				print("error on: ",type(args[0]).__name__+"."+janh)
# 				assert ahjs.verified


# 		if janh == "substitute":
# 			# if args[0].verified and len(args[2]) == 0 and not ahjs.verified:
# 			# 	print("error on: ",type(args[0]).__name__+"."+janh)
# 			# 	assert False

# 			if args[0].verified and not ahjs.verified:
# 				for i in args[2].subs:
# 					if not (i.obj.verified and (type(i.obj) is not ObjKindUnionSet or i.obj.verprot == 1)):
# 						break
# 				else:
# 					print("error on: ",type(args[0]).__name__+"."+janh)
# 					print("to elaborate: ",args[0],args[1],args[2].subs)
# 					assert False

# 	return wrapper









