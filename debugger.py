import ast
import sys
import time
from ast import Expr,Call,Attribute,Name,Load,Num,With,Store,Str,Assign,Return,FunctionDef,withitem,NameConstant
from pycallgraph import PyCallGraph
from pycallgraph.output import GraphvizOutput


class Madscience_debug_context:
	def __init__(self,id,owner):
		self.id = id
		self.modifiers = []
		self.owner = owner
	def log(self,mod):
		# print("logged",mod)
		if mod not in self.modifiers: self.modifiers.append(mod)
	def __enter__(self):
		self.owner.stack.append(self)
		# print("entering:",self.owner.readable_path())
		return self
	def freeze(self):
		return tuple([self.id]+sorted(self.modifiers))
	def __exit__(self,type,value,traceback):
		# print(type,value,traceback)
		if value == None:
			key = self.freeze()
			if key in self.owner.encounters:
				self.owner.encounters[key]+=1
			else:
				self.owner.encounters[key] = 1
		else:
			# print("there was an error:",type,value,self.owner.readable_path())
			if not hasattr(value,'madscience_stack'):
				value.madscience_stack = self.owner.freeze_stack()
		# assert self.owner.stack.pop() is self
		self.owner.stack.pop()

class Madscience_debugger(ast.NodeTransformer):
	def __init__(self,enableCodeCoverage=False):
		self.funcNames = []
		self.funcparams = []
		self.classowners = []
		self.scopes = []
		self.hot = 0
		self.hotHasReturnCheck = False
		self.hot = None
		self.encounters = {}
		self.stack = []
		self.enterpatterns = {}
		self.exitpatterns = {}
		self.enableCodeCoverage = enableCodeCoverage
	def has_number_args(self,args,n):
		return len(args.args)==n and args.vararg==None and args.kwonlyargs==[] and args.kw_defaults==[] and args.kwarg==None
	def isTestFunc(self,func):
		if type(func) is not FunctionDef: return False
		if func.name!='_dbgTest': return False
		assert self.has_number_args(func.args,0)
		return True
	def isEnterFunc(self,func):
		if type(func) is not FunctionDef: return False
		if func.name!='_dbgEnter': return False
		assert self.has_number_args(func.args,0)
		return True
	def isExitFunc(self,func,supargs):
		if type(func) is not FunctionDef: return False
		if func.name!='_dbgExit': return False
		assert self.has_number_args(func.args,1)
		func.args.args = supargs+func.args.args
		return True


	def absorbEnterPattern(self,func):
		if not func.name.startswith('_dbgEnter_'): return False
		key = func.name[len('_dbgEnter_'):]
		assert key not in self.enterpatterns
		self.enterpatterns[key] = [k.arg for k in func.args.args]
	def absorbExitPattern(self,func):
		if not func.name.startswith('_dbgExit_'): return False
		key = func.name[len('_dbgExit_'):]
		assert key not in self.exitpatterns
		self.exitpatterns[key] = [k.arg for k in func.args.args[:-1]]

	def freeze_stack(self):
		return [k.freeze() for k in self.stack]
	def push_context(self,id):
		return Madscience_debug_context(id,self)
	def readable_path(self):
		return "/".join([self.funcNames[i.id] for i in self.stack])
	def visit_ClassDef(self,node:ast.ClassDef):
		for j in node.body:
			if isinstance(j,FunctionDef):
				j.definedforclass = node.name
		self.generic_visit(node)
		return node
	def visit_Return(self,node:ast.Return):
		if self.hot == None or (not self.hotHasReturnCheck and self.funcNames[self.hot] not in self.exitpatterns): return node
		# print("Assign: ",self.funcNames[self.hot])
		sin = [
			Assign(targets=[Name(id='_dbg_ret_var', ctx=Store())], value=node.value),
			Return(value=Name(id='_dbg_ret_var', ctx=Load()))
		]
		if self.hotHasReturnCheck:
			expattern = self.funcparams[self.hot]
			sin.insert(1,Expr(value=Call(func=Name(id='_dbgExit', ctx=Load()), args=[Name(id=pn+'_dbg_str_var_'+str(self.hot),ctx=Load()) for pn in expattern]+[Name(id='_dbg_ret_var', ctx=Load())], keywords=[])))
		if self.funcNames[self.hot] in self.exitpatterns:
			expattern = self.exitpatterns[self.funcNames[self.hot]]
			sin.insert(1,Expr(value=Call(func=Name(id='_dbgExit_'+self.funcNames[self.hot],ctx=Load()), args=[Name(id=pn+'_dbg_str_var_'+str(self.hot),ctx=Load()) for pn in expattern]+[Name(id='_dbg_ret_var', ctx=Load())], keywords=[])))
		for s in sin:
			ast.copy_location(s, node)
			ast.fix_missing_locations(s)
		return sin
	def visit_FunctionDef(self, node: ast.FunctionDef):
		if len(node.body)>0 and isinstance(node.body[0],Expr) and isinstance(node.body[0].value,Str) and node.body[0].value.s == 'dbg_ignore':
			oldHHRC = self.hotHasReturnCheck
			oldBV = self.hot
			self.hotHasReturnCheck = False
			self.hot = None
			self.generic_visit(node)
			self.hotHasReturnCheck = oldHHRC
			self.hot = oldBV
			return node
		# print("visiting",node.name)
		frozone = len(self.funcNames)
		self.funcNames.append(node.name)#+str(node.lineno)
		if hasattr(node,'definedforclass'):
			self.classowners.append(node.definedforclass)
		else:
			self.classowners.append(None)
		self.scopes.append(0)
		self.funcparams.append([k.arg for k in node.args.args])
		hasEnter = False
		hasExit = False
		fpad = 2
		if len(node.body)>0:
			if  self.isEnterFunc(node.body[0]): hasEnter=True
			elif self.isExitFunc(node.body[0],node.args.args): hasExit=True
			else: fpad-=1
		else: fpad-=1
		if len(node.body)>1:
			if  self.isEnterFunc(node.body[1]): hasEnter=True
			elif self.isExitFunc(node.body[1],node.args.args): hasExit=True
			else: fpad-=1
		else: fpad-=1

		oldHHRC = self.hotHasReturnCheck
		oldBV = self.hot
		self.hotHasReturnCheck = hasExit
		self.hot = frozone
		self.generic_visit(node)


		if len(self.exitpatterns.get(node.name,[])) > len(node.args.args):
			print("Exit pattern for function ",node.name," has too many parameters.")
			assert False

		shobb = []
		for z in range(len(node.args.args) if hasExit else len(self.exitpatterns.get(node.name,[]))):
			# print("Assign2: ",str(frozone))
			shobb.append(Assign(
				targets=[Name(id=node.args.args[z].arg+'_dbg_str_var_'+str(frozone), ctx=Store())],
				value=Name(id=node.args.args[z].arg,ctx=Load())
			))

		if hasExit:
			expattern = [k.arg for k in node.args.args]
			# sin.insert(1,Expr(value=Call(func=Name(id='_dbgExit', ctx=Load()), args=[Name(id=pn+'_dbg_str_var_'+str(self.hot),ctx=Load()) for pn in expattern]+[Name(id='_dbg_ret_var', ctx=Load())], keywords=[])))


			node.body.append(Expr(value=Call(func=Name(id='_dbgExit', ctx=Load()), args=[Name(id=pn+'_dbg_str_var_'+str(self.hot),ctx=Load()) for pn in expattern]+[NameConstant(value=None)], keywords=[])))
		if node.name in self.exitpatterns:
			expattern = self.exitpatterns[node.name]
			if len(node.args.args)<len(expattern) or expattern != [k.arg for k in node.args.args][:len(expattern)]:
				print("You defined an exit pattern, "+node.name+", and then you define a function with different first N parameters from it.")
				assert False


			node.body.append(Expr(value=Call(func=Name(id='_dbgExit_'+node.name, ctx=Load()), args=[Name(id=pn+'_dbg_str_var_'+str(self.hot),ctx=Load()) for pn in expattern]+[NameConstant(value=None)], keywords=[])))




		node.body = [
			*shobb,
			*node.body[:fpad],
			With(
				items=[
					withitem(
						context_expr=Call(func=Attribute(value=Name(id='madscience_debugger', ctx=Load()), attr='push_context', ctx=Load()), args=[Num(n=frozone)], keywords=[]),
						optional_vars=Name(id='madscience_debug_context', ctx=Store())
					)
				],
				body=node.body[fpad:]+[]
			)
		]

		self.visitblock(node.body[-1].body,"func")
		# if node.name=="verify":
		# 	print("verify mutated",node.lineno)
		# 	node.body.insert(0,Expr(value=Call(func=Name(id='print', ctx=Load()), args=[Str(s='function was knocked on '+str(node.lineno))], keywords=[])))
		# 	node.body[-1].body.insert(0,Expr(value=Call(func=Name(id='print', ctx=Load()), args=[Str(s='function was visited '+str(node.lineno))], keywords=[])))
		# print("mutated",node.name)
		# print(self.enterpatterns,frozone,node.name)
		if hasEnter: node.body.insert(fpad+len(shobb),Expr(value=Call(func=Name(id='_dbgEnter', ctx=Load()), args=[], keywords=[])))
		if node.name in self.enterpatterns:
			# print("enter pattern added.")
			expattern = self.enterpatterns[node.name]
			if len(node.args.args)<len(expattern) or expattern != [k.arg for k in node.args.args][:len(expattern)]:
				print("You defined an enter pattern, "+node.name+", and then you define a function with different first N parameters from it.")
				assert False
			node.body.insert(fpad+len(shobb),Expr(value=Call(func=Name(id='_dbgEnter_'+node.name, ctx=Load()), args=[Name(id=pn,ctx=Load()) for pn in expattern], keywords=[])))
		ast.fix_missing_locations(node)
		if self.isTestFunc(node):
			# self.generic_visit(node)
			sin = [
				node,
				Expr(value=Call(func=Name(id='_dbgTest', ctx=Load()), args=[], keywords=[]))
			]
			ast.copy_location(sin[1], node)
			ast.fix_missing_locations(sin[1])
			return sin
		self.absorbEnterPattern(node)
		self.absorbExitPattern(node)
		# print()
		# print(ast.dump(node))
		self.hotHasReturnCheck = oldHHRC
		self.hot = oldBV



		return node
	def visitblock(self,body,kind):
		if not self.enableCodeCoverage: return
		if self.hot == None: return
		for i in reversed(range(len(body)+1)):
			versneaky0 = Expr(value=Call(func=Attribute(value=Name(id='madscience_debug_context', ctx=Load()), attr='log', ctx=Load()), args=[Num(n=self.scopes[self.hot]+i)], keywords=[]))
			body.insert(i,versneaky0)
		self.scopes[self.hot]+=len(body)
	def visit_If(self, node: ast.If):
		self.generic_visit(node)
		self.visitblock(node.body,"if")
		# if len(node.orelse)>0 and (len(node.orelse) != 1 or type(node.orelse[0]) is not ast.If):
		self.visitblock(node.orelse,"else")
		ast.fix_missing_locations(node)
		return node
	def visit_For(self, node: ast.For):
		self.generic_visit(node)
		self.visitblock(node.body,"for")
		self.visitblock(node.orelse,"forelse")
		ast.fix_missing_locations(node)
		return node
	def visit_While(self, node: ast.While):
		self.generic_visit(node)
		self.visitblock(node.body,"while")
		self.visitblock(node.orelse,"whileelse")
		ast.fix_missing_locations(node)
		return node
	def visit_With(self, node: ast.With):
		self.generic_visit(node)
		self.visitblock(node.body,"with")
		ast.fix_missing_locations(node)
		return node
	def visit_ExceptHandler(self, node: ast.ExceptHandler):
		self.generic_visit(node)
		self.visitblock(node.body,"exceptHandler")
		ast.fix_missing_locations(node)
		return node
	def visit_Try(self, node: ast.Try):
		self.generic_visit(node)
		self.visitblock(node.body,"try")
		self.visitblock(node.orelse,"tryelse")
		self.visitblock(node.finalbody,"finally")
		ast.fix_missing_locations(node)
		return node



	def previously_covered(self,elem):
		tamt = 0
		se = list(elem)[1:]
		for j,o in self.encounters.items():
			if j[0]==elem[0]:
				se = [k for k in se if k not in j[1:]]
				tamt += o
		# print("percentage:",se,elem)
		return (100 if len(elem)==1 else (100-  (float(len(se))*100.0/float(len(elem)-1))   )     ,tamt  )
	def readable_stacktrace_element(self,elem):
		# sres = []
		# for k in elem[1:]:
			# thiskind = self.scopes[elem[0]][k][0]
			# index = 0
			# total = 0
			# for h in range(k):
			# 	if self.scopes[elem[0]][h][0] == thiskind: index+=1
			# for h in range(len(self.scopes[elem[0]])):
			# 	if self.scopes[elem[0]][h][0] == thiskind: total+=1
			# sres.append(thiskind+"("+str(index+1)+"/"+str(total)+")")
		# res = self.funcNames[elem[0]]+" "+",".join(sres)

		# print(line," "*(maxlen-len(line)),"<---- (%3.2f% Previously covered; %d Calls)" % self.previously_covered(elem))
		res = self.funcNames[elem]
		if self.classowners[elem] != None: res = self.classowners[elem]+"."+res
		return res
	def readable_stacktrace(self,stacktrace):
		print("MS Traceback (most recent call last):")
		# print(stacktrace)
		lines  = [self.readable_stacktrace_element(elem[0]) for elem in stacktrace]
		# print(lines)
		maxlen = max([len(line) for line in lines])
		for e in range(len(stacktrace)):
			line = lines[e]
			elem = stacktrace[e]

			print(line," "*(maxlen-len(line)),"<---- (%3.0f%% Previously covered; %d Calls)" % self.previously_covered(elem))
	def numcalls(self):
		jnum = {}
		for j,o in self.encounters.items():
			if j[0] in jnum:jnum[j[0]]+=o
			else:jnum[j[0]]=o
		maxlen = max([len(self.readable_stacktrace_element(ind)) for ind,amt in jnum.items()])
		for ind,amt in sorted(jnum.items(), key = lambda kv:(kv[1], kv[0])):
			hya = self.readable_stacktrace_element(ind)
			if ".verify" not in hya and ".flatten" not in hya and "symextract" not in hya: continue
			print(hya," "*(maxlen-len(hya))," called %d times." % amt)

		# 	if elem not in self.encounters:


		# # self.previously_covered(elem)


		# 		really = True
		# 		for k in self.encounters.keys():
		# 			if k[0]==elem[0]:
		# 				really = False
		# 		if really:
		# 			print(line," "*(maxlen-len(line)),"<---- (really suspicious)")
		# 		else:
		# 			print(line," "*(maxlen-len(line)),"<---- (suspicious)")
		# 	else:
		# 		print(line," "*(maxlen-len(line)),"<--("+str(self.encounters[elem])+" previous encounters)")



#to make this happen, walk over subsets of code to detect any kind of skip
	#it'd have to be a smart traversal- breaks inside for loops don't count.
	#function definitions also don't count although i doubt that would be a problem.







#you automatically have 0.




# print(ast.dump(ast.parse("""

# while(True):
# 	pass
# else:
# 	pass

# """)))
# assert False
#Try(body=[Pass()], handlers=[ExceptHandler(type=None, name=None, body=[Pass()])], orelse=[Pass()], finalbody=[Pass()])


if len(sys.argv)!=2:
	print("Usage: python3 science.py [target]")
	assert False

#percentage of code coverage instead of 'sus'...
#gna need With, Try(all that jazz)
#when registering scopes, also register shallow line count.

#all values returned from functions get a flag...
#all parameters that break an input verification (or output ahjs, i guess) could get their origin tracebacks printed.

filename = sys.argv[1]
with open(filename, encoding='utf-8') as f: code = f.read()


madscience_debugger = Madscience_debugger(False)

test_namespace = {'madscience_debugger': madscience_debugger}

tree = ast.parse(code)
tree = madscience_debugger.visit(tree)

# def ismyprintline(node):
# 	return isinstance(node, ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='print' and len(node.args)==1 and type(node.args[0]) is ast.Str and node.args[0].s=="nope"

# for node in ast.walk(tree):
# 	if isinstance(node, ast.FunctionDef) and node.name == "verify":
# 		print("-=-",node.lineno)
# 		for sub in node.body:
# 			print("\t",type(sub))

# 	if ismyprintline(node):
# 		print("awakawaka")
	# if type(tree) is
# print(tree,filename)

# print(tree)
co = compile(tree, filename, 'exec')
try:
	start = time.time()
	# with PyCallGraph(output=GraphvizOutput()):
	exec(co, test_namespace)
	end = time.time()
	print("elapsed time:",end - start)
	madscience_debugger.numcalls();
except Exception as u:
	if hasattr(u,'madscience_stack'):
		madscience_debugger.readable_stacktrace(u.madscience_stack)
	else:
		print("Madscience did not catch any errors...")
	raise u


#4.713582992553711





# arg(arg='a', annotation=None),
# arg(arg='b', annotation=None),
# arg(arg='c', annotation=None),
# arg(arg='d', annotation=None),
# arg(arg='e', annotation=None)





# Module(body=[


# FunctionDef(name='momomo',


# args=arguments(,
# vararg=None,
# kwonlyargs=[],
# kwarg=None,<><>

# kw_defaults=[],
# defaults=[NameConstant(value=None), NameConstant(value=None)]), body=[Pass()], decorator_list=[], returns=None)])
















