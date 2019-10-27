import ast
import sys
from ast import Expr,Call,Attribute,Name,Load,Num,With,Store,Str,Assign,Return,FunctionDef,withitem,NameConstant


class Madscience_debug_context:
	def __init__(self,id,owner):
		self.id = id
		self.modifiers = []
		self.owner = owner
	def log(self,mod):
		if mod not in self.modifiers: self.modifiers.append(mod)
	def __enter__(self):
		self.owner.stack.append(self)
		return self
	def freeze(self):
		return tuple([self.id]+sorted(self.modifiers))
	def __exit__(self,type,value,traceback):
		if value == None:
			key = self.freeze()
			if key in self.owner.encounters:
				self.owner.encounters[key]+=1
			else:
				self.owner.encounters[key] = 1
		else:
			if not hasattr(value,'madscience_stack'):
				value.madscience_stack = self.owner.freeze_stack()
		assert self.owner.stack.pop() is self


class Madscience_debugger(ast.NodeTransformer):
	def __init__(self):
		self.funcNames = []
		self.scopes = []
		self.buildvis = 0
		self.hotHasReturnCheck = False
		self.encounters = {}
		self.stack = []
	def has_number_args(self,args,n):
		return len(args.args)==n and args.vararg==None and args.kwonlyargs==[] and args.kw_defaults==[] and args.kwarg==None and args.defaults==[]
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
	def isExitFunc(self,func):
		if type(func) is not FunctionDef: return False
		if func.name!='_dbgExit': return False
		assert self.has_number_args(func.args,1)
		return True
	def freeze_stack(self):
		return [k.freeze() for k in self.stack]
	def storeStack(self,type,value,traceback):
		self.hottraceback = traceback
		self.hotstack = copy.copy(self.stack)
	def push_context(self,id):
		return Madscience_debug_context(id,self)
	def readable_path(self):
		return "/".join([self.funcNames[i.id] for i in self.stack])
	def visit_Return(self,node:ast.Return):
		if not self.hotHasReturnCheck: return node
		sin = [
			Assign(targets=[Name(id='_dbg_ret_var', ctx=Store())], value=node.value),
			Expr(value=Call(func=Name(id='_dbgExit', ctx=Load()), args=[Name(id='_dbg_ret_var', ctx=Load())], keywords=[])),
			Return(value=Name(id='_dbg_ret_var', ctx=Load()))
		]
		ast.copy_location(sin[0], node)
		ast.copy_location(sin[1], node)
		ast.copy_location(sin[2], node)
		ast.fix_missing_locations(sin[0])
		ast.fix_missing_locations(sin[1])
		ast.fix_missing_locations(sin[2])
		return sin
	def visit_FunctionDef(self, node: ast.FunctionDef):
		frozone = len(self.funcNames)
		self.funcNames.append(node.name)
		self.scopes.append([])
		hasEnter = False
		hasExit = False
		fpad = 2
		if len(node.body)>0:
			if  self.isEnterFunc(node.body[0]): hasEnter=True
			elif self.isExitFunc(node.body[0]): hasExit=True
			else: fpad-=1
		else: fpad-=1
		if len(node.body)>1:
			if  self.isEnterFunc(node.body[1]): hasEnter=True
			elif self.isExitFunc(node.body[1]): hasExit=True
			else: fpad-=1
		else: fpad-=1
		oldHHRC = self.hotHasReturnCheck
		oldBV = self.buildvis
		self.hotHasReturnCheck = hasExit
		self.buildvis = frozone
		self.generic_visit(node)
		self.hotHasReturnCheck = oldHHRC
		self.buildvis = oldBV
		if hasExit: node.body.append(Expr(value=Call(func=Name(id='_dbgExit', ctx=Load()), args=[NameConstant(value=None)], keywords=[])))
		node.body = [
			*node.body[:fpad],
			With(
				items=[
					withitem(
						context_expr=Call(func=Attribute(value=Name(id='madscience_debugger', ctx=Load()), attr='push_context', ctx=Load()), args=[Num(n=frozone)], keywords=[]),
						optional_vars=Name(id='madscience_debug_context', ctx=Store())
					)
				],
				body=node.body[fpad:]
			)
		]
		if hasEnter: node.body.insert(fpad,Expr(value=Call(func=Name(id='_dbgEnter', ctx=Load()), args=[], keywords=[])))
		ast.fix_missing_locations(node)
		if self.isTestFunc(node):
			self.generic_visit(node)
			sin = [
				node,
				Expr(value=Call(func=Name(id='_dbgTest', ctx=Load()), args=[], keywords=[]))
			]
			ast.copy_location(sin[1], node)
			ast.fix_missing_locations(sin[1])
			return sin
		return node
	def visitblock(self,body,kind):
		self.scopes[self.buildvis].append(kind)
		versneaky0 = Expr(value=Call(func=Attribute(value=Name(id='madscience_debug_context', ctx=Load()), attr='log', ctx=Load()), args=[Num(n=len(self.scopes[self.buildvis])-1)], keywords=[]))
		body.insert(0,versneaky0)
	def visit_If(self, node: ast.If):
		self.generic_visit(node)
		self.visitblock(node.body,"if")
		if len(node.orelse)>0 and (len(node.orelse) != 1 or type(node.orelse[0]) is not ast.If):
			self.visitblock(node.orelse,"else")
		ast.fix_missing_locations(node)
		return node
	def visit_For(self, node: ast.For):
		self.generic_visit(node)
		self.visitblock(node.body,"for")
		ast.fix_missing_locations(node)
		return node
	def visit_While(self, node: ast.While):
		self.generic_visit(node)
		self.visitblock(node.body,"while")
		ast.fix_missing_locations(node)
		return node
	def readable_stacktrace_element(self,elem):
		sres = []
		for k in elem[1:]:
			thiskind = self.scopes[elem[0]][k]
			index = 0
			total = 0
			for h in range(k):
				if self.scopes[elem[0]][h] == thiskind: index+=1
			for h in range(len(self.scopes[elem[0]])):
				if self.scopes[elem[0]][h] == thiskind: total+=1
			sres.append(thiskind+"("+str(index+1)+"/"+str(total)+")")
		return self.funcNames[elem[0]]+" "+",".join(sres)
	def readable_stacktrace(self,stacktrace):
		print("MS Traceback (most recent call last):")
		lines  = [self.readable_stacktrace_element(elem) for elem in stacktrace]
		maxlen = max(*[len(line) for line in lines])
		for e in range(len(stacktrace)):
			line = lines[e]
			elem = stacktrace[e]
			if elem not in self.encounters:
				print(line," "*(maxlen-len(line)),"<---- (suspicious)")
			else:
				print(line," "*(maxlen-len(line)),"<--("+str(self.encounters[elem])+" previous encounters)")


if len(sys.argv)!=1:
	print("Usage: python3 science.py [target]")


filename = sys.argv[1]
with open(filename, encoding='utf-8') as f: code = f.read()


madscience_debugger = Madscience_debugger()

test_namespace = {'madscience_debugger': madscience_debugger}

tree = ast.parse(code)
tree = madscience_debugger.visit(tree)
co = compile(tree, filename, 'exec')
try:
	exec(co, test_namespace)
except Exception as u:
	if hasattr(u,'madscience_stack'):
		madscience_debugger.readable_stacktrace(u.madscience_stack)
		raise u
	else:
		print("Madscience did not catch any errors...")
		raise u







