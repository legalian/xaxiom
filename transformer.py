
from lark import Transformer, v_args, Tree
from .simplifier import *

@v_args(meta=True)
class MyTransformer(Transformer):
	def start(self,children,meta):
		return (children[:-1],children[-1])
	def precrow(self,children,meta):
		if type(children[-1]) is dict:
			return (children[:-1],children[-1])
		return (children,{'associate':'left'})
	def leftassoc(self,children,meta):
		return {'associate':'left'}
	def rightassoc(self,children,meta):
		return {'associate':'right'}
#--------------------------------------------------
	def argument(self,children,meta):
		if type(children[0]) is str: return SubRow([k.replace("*****",".") for k in children[0].replace("'.'","*****").split(".")],children[1])
		return SubRow(None,children[0])
	def datapack(self,children,meta):
		if type(children[0]) is str or type(children[0]) is list: return (children[0],children[1])
		return ("*****",children[0])
	def declaration(self,children,meta):
		if type(children[0]) is tuple:
			obj = None
			if len(children)>2:
				obj = children[2]
				if type(children[1]) is Strategy:
					obj = Lambda(children[1].args.semavail(),obj)
			return TypeRow(children[0][0],children[1],obj,children[0][1])
		obj = None
		if len(children)>1:
			obj = children[1]
			if type(children[0]) is Strategy:
				obj = Lambda(children[0].args.semavail(),obj)
		return TypeRow(None,children[0],obj,{'silent':False,'contractible':False})
	def inferreddeclaration(self,children,meta):
		ty = None if len(children)<3 else Strategy(args=children[1],type=None)
		return TypeRow(children[0][0],ty,children[-1],children[0][1])
	def interrobangmarker(self,children,meta):
		return {'silent':True,'contractible':True}
	def silentmarker(self,children,meta):
		return {'silent':True,'contractible':False}
	def contractmarker(self,children,meta):
		return {'silent':False,'contractible':True}
	def infermarker(self,children,meta):
		return {'silent':False,'contractible':False}
	def multilabel(self,children,meta):
		return children[0]
	def introducer(self,children,meta):
		return children
	def reftree(self,children,meta):
		if type(children[0]) is str:
			src = None
			name = children[0]
			lim = 1
		else:
			src = children[0]
			name = children[1]
			lim = 2
		safety = None
		args = []
		for j in children[lim:]:
			if safety==None: safety = len(j.subs)
			args += j.subs
		return RefTree(name,SubsObject(args),src,safety,pos=meta)
	def lamb(self,children,meta):
		return Lambda(children[0],children[1],pos=meta)
	def template(self,children,meta):
		if len(children): return Template(children[0],children[1],pos=meta)
		return Template(children[0],SubsObject(pos=meta),pos=meta)
	def strategy(self,children,meta):
		args = []
		for j in children[:-1]:
			args += j.rows
		return Strategy(DualSubs(args),children[-1],pos=meta)
	def string(self,children,meta):
		if str(children[0]).endswith(".ax'"): return str(children[0])
		return str(children[0]).replace("'","")
	def operators(self,children,meta):
		return OperatorSet(children,pos=meta)
	def subsobject(self,children,meta):
		return SubsObject(children,pos=meta)
	def wsubsobject(self,children,meta):
		return children[0] if len(children) else SubsObject(pos=meta)
	def dualsubs(self,children,meta):
		return DualSubs(children,pos=meta)
	def wdualsubs(self,children,meta):
		return children[0] if len(children) else DualSubs(pos=meta)

