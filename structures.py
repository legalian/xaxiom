import sublime, sublime_plugin
from lark import Lark, UnexpectedInput
import copy


class Statement:
	def __init__(self,args=[],parsed=None,name=None,lvlup=None,id=None,local=None,pos=None):
		self.id = id
		self.local = local
		self.lvlup = lvlup
		self.column = 0
		self.row = 0
		if lvlup == None:
			self.lvlup = [[] for a in args]
		self.args = args
		self.name = name
		if pos != None:
			self.column = pos.column-1
			self.row = pos.line-1
		if parsed != None:
			assert len(args)==0
			self.name = parsed[0]
			self.lvlup      = [[f for f in k.children[:-1]] for k in parsed[1:]]
			self.args       = [k.children[-1] for k in parsed[1:]]
	def __str__(self):
		if self.name == None:
			if len(self.args)!=0: return "~anon~("+",".join([str(k) for k in self.args])+")"
			return "~anon~"
		if len(self.args)!=0: return self.name+"("+",".join([str(k) for k in self.args])+")"
		return str(self.name)
	def purestring(self):
		if len(self.args)!=0: return "{"+str(self.local)+"/"+str(self.id)+"}("+",".join([k.purestring() for k in self.args])+")"
		return "{"+str(self.local)+"/"+str(self.id)+"}"

	def __eq__(self,other):
		if self.id == None or other.id == None: return False
		if self.local == None or other.local == None: return False
		if self.id != other.id: return False
		if self.local != other.local: return False
		if len(self.args) != len(other.args): return False
		for arg in range(len(self.args)):
			if self.args[arg] != other.args[arg]: return False
		return True
	def comparableTo(self,other):
		if self.id == None or other.id == None: return True
		if self.local == None or other.local == None: return True
		if self.id != other.id: return True
		if self.local != other.local: return True
		if len(self.args) != len(other.args): return False
		for arg in range(len(self.args)):
			if not self.args[arg].comparableTo(other.args[arg]): return False
		return True
	def formalize(self,scope,errors):
		if self.name == "~":
			errors.append((self.row,self.column,4,self.name))
			return
		sig = scope.getfromname(self.name)

		typ = self.generatetype(scope)

		if sig == None:
			errors.append((self.row,self.column,2,self.name))
			return
		sig = sig[2]
		if len(sig.args)!=len(self.args):
			errors.append((self.row,self.column,3,self.name))
			return
		if len(self.args) != len(self.lvlup):
			errors.append((self.row,self.column,0,self.name))
			return
		if typ == None:
			errors.append((self.row,self.column,1,self.name))
			return
		for blah in range(len(self.args)):
			self.args[blah].formalize(scope.append(typ.args[blah].args),errors)

	def apply(self,scope,head=None,carry=None,tail=None):
		dlen = head(self,scope,carry)
		if self.local == None: return None
		assert len(self.args) == len(self.lvlup)
		typ = self.generatetype(scope)
		if typ == None: return None
		vorp = []
		for blah in range(len(self.args)):
			dl = dlen[blah] if dlen is not None else None
			vorp.append(self.args[blah].apply(scope.append(typ.args[blah].args),head=head,carry=dl,tail=tail))
		if tail == None: return
		return tail(self,vorp)
	def copy(self):
		jol = Statement([a.copy() for a in self.args],lvlup=copy.deepcopy(self.lvlup),name=self.name,id=self.id,local=self.local)
		jol.column = self.column
		jol.row = self.row
		return jol
	def substitute(self,slevel,inc,repl,recur=0):
		if self.local == None or self.id == None: return self.copy()
		if self.local==slevel:
			fargs = [a.substitute(slevel,inc,repl,recur+1) for a in self.args]
			return repl[self.id].substitute(slevel+inc,recur,fargs)
		else:
			nlocal = self.local+inc-1 if self.local>slevel else self.local
			nargs = [a.substitute(slevel,inc,repl,recur+1) for a in self.args]
			jol = Statement(nargs,lvlup=copy.deepcopy(self.lvlup),name=self.name,id=self.id,local=nlocal)
			jol.column = self.column
			jol.row = self.row
			return jol
	def depthpush(self,slevel,inc):
		if self.local == None: return self.copy()
		jol = Statement([a.depthpush(slevel,inc) for a in self.args],lvlup=copy.deepcopy(self.lvlup),name=self.name,id=self.id,local=self.local if self.local<slevel else self.local+inc)
		jol.column = self.column
		jol.row = self.row
		return jol
	def generatetype(self,scope):
		if self.local != None:
			strat = scope.get(self.local,self.id)
		elif self.name != None:
			typ = scope.getfromname(self.name)
			if typ == None: return None
			strat = typ[2]
			self.local = typ[0]
			self.id = typ[1]
		else: return None
		if strat == None: return None
		strat = strat.substitute(self.local+1,len(scope.rows)-1-self.local,self.args)

		if len(self.lvlup)!= 0:
			for sn in range(len(strat.args)):
				if len(self.lvlup[sn])!=0:
					for kr in range(len(strat.args[sn].args)):
						strat.args[sn].rename(kr,self.local+2,self.lvlup[sn][kr])
						strat.args[sn].args[kr].name = self.lvlup[sn][kr]

		return strat
	def rename(self,id,local,name):
		if self.id == id and self.local == local:
			self.name = name
		for arg in self.args:
			arg.rename(id,local,name)

class Strategy:
	def __init__(self,args=[],parsed=None,ty=None,name=None,pos=None):
		self.args = args
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
			self.type = parsed[-1]
			if len(parsed)>1 and parsed[-2].data == 'label':
				self.name = parsed[-2]
				self.args = [m for m in multistrat(arg) for arg in parsed[0:-2]]
			else:
				self.args = [m for m in multistrat(arg) for arg in parsed[0:-1]]
	def __str__(self):
		if len(self.args) != 0:
			if self.name != None: return "["+",".join([str(k) for k in self.args])+"]"+self.name+":"+str(self.type)
			else: return "["+",".join([str(k) for k in self.args])+"]"+str(self.type)
		else:
			if self.name != None: return self.name+":"+str(self.type)
			else: return str(self.type)
	def purestring(self):
		if len(self.args)!=0: return "["+",".join([m.purestring() for m in self.args])+"]"+self.type.purestring()
		return self.type.purestring()
	def formalize(self,scope,errors):
		for blah in range(len(self.args)):
			if len(scope.rows)==0 and blah==0: gah = scope.append(self.args[:1])
			else: gah = scope.append(self.args[:blah])
			self.args[blah].formalize(gah,errors)
		gah = scope.append(self.args)
		self.type.formalize(gah,errors)
	def apply(self,scope,head=None,carry=None,tail=None):
		for blah in range(len(self.args)):
			if len(scope.rows)==0 and blah==0: gah = scope.append(self.args[:1])
			else: gah = scope.append(self.args[:blah])
			self.args[blah].apply(gah,head=head,carry=carry,tail=tail)
		gah = scope.append(self.args)
		self.type.apply(gah,head=head,carry=carry,tail=tail)
	def copy(self):
		jol = Strategy([a.copy() for a in self.args],ty=self.type.copy(),name=self.name)
		jol.column = self.column
		jol.row = self.row
		return jol
	def depthpush(self,slevel,inc):
		jol = Strategy([a.depthpush(slevel,inc) for a in self.args],ty=self.type.depthpush(slevel,inc),name=self.name)
		jol.column = self.column
		jol.row = self.row
		return jol
	def substitute(self,slevel,inc,repl,recur=0):
		jol = Strategy([a.substitute(slevel,inc,repl,recur+1) for a in self.args],ty=self.type.substitute(slevel,inc,repl,recur),name=self.name)
		jol.column = self.column
		jol.row = self.row
		return jol
	def rename(self,id,local,name):
		for arg in self.args:
			arg.rename(id,local,name)
		self.type.rename(id,local,name)

def multistrat(parsed):
	args = [m for arg in parsed[0:-1] for m in arg]
	if isinstance(parsed[-1].children[0],list):
		extr = [m for arg in parsed[-1].children for m in arg]
	else:
		if len(parsed[-1].children)==1:
			extr = [Strategy(ty=parsed[-1].children[-1])]
		else:
			extr = [Strategy(name=parsed[-1].children[0],ty=parsed[-1].children[-1])]

	for g in extr:
		g.args = [j.copy() for j in args] + g.args
	return extr
def snapshothelper(local,id,ob):
	jol = Statement([snapshothelper(local+1,a,ob.args[a]) for a in range(len(ob.args))],name=ob.name,id=id,local=local)
	jol.column = ob.column
	jol.row = ob.row
	return jol



class Scope:
	def __init__(self,rows):
		self.rows = [[col for col in row] for row in rows]
		pass
	def copy(self):
		return Scope(self.rows)
		pass
	def append(self,row):
		return Scope(self.rows+[[(k.name,k) for k in row]])
		pass
	def get(self,local,id):
		if local>=len(self.rows): return None
		if id>=len(self.rows[local]): return None
		return self.rows[local][id][1]
	def getname(self,local,id):
		if local>=len(self.rows): return None
		if id>=len(self.rows[local]): return None
		return self.rows[local][id][0]
	def getfromname(self,key):
		for row in reversed(range(len(self.rows))):
			for col in range(len(self.rows[row])):
				if self.rows[row][col][0]==key:
					return (row,col,self.rows[row][col][1])
		return None

class Stitching:
	def __init__(self,scope):
		self.scope = scope
		self.stitches = []
		self.valid = True
	def compare(self,l,r,scope=None):
		if scope == None: scope = self.scope
		if l.id is None or r.id is None or l.local is None or r.local is None:
			self.valid = False
		elif l.local == len(self.scope.rows)-1 or r.local == len(self.scope.rows)-1:
			self.stitches.append((scope,l.copy(),r.copy()))
		elif l.id != r.id or l.local != r.local:
			self.valid = False
		else:
			typ = l.generatetype(scope)
			for y in range(len(l.args)):
				self.compare(l.args[y],r.args[y],scope.append(typ.args[y].args))


def typecheck(self,scope,errors):
	def nhead(self,scope,carry):
		if carry is None or self.local == None: return
		typ = self.generatetype(scope)
		if typ == None:
			errors.append((carry,None,None,self.row,self.column))
			return
		typ.name = None
		for jar in typ.args:
			jar.name = None
		sig = scope.get(self.local,self.id)
		if carry.comparableTo(typ.type) and carry != typ.type:
			errors.append((carry,sig,typ,self.row,self.column))
			return
		return [a.type for a in typ.args]
	self.apply(scope,head=nhead,carry=Statement([],name="U",id=0,local=0))
def diagnostics(self,scope,ranges,view,reports):
	def nhead(self,scope,carry):
		method = 0 if self.local != None else 1

		k = view.text_point(self.row,self.column)
		typ = self.generatetype(scope)
		sig = None
		if typ == None:
			if k in ranges:
				reports.append((carry,None,None,self.row,self.column))
			return



		sig = scope.get(self.local,self.id)
		typ.name = None
		for jar in typ.args:
			jar.name = None
		if k in ranges:
			reports.append((carry,sig,typ,self.row,self.column,method))
		return [a.type for a in typ.args]
	self.apply(scope,head=nhead,carry=Statement([],name="U",id=0,local=0))
def holeanalysis(self,scope,reports):
	def nhead(self,scope,carry):
		if carry is None: return
		if self.name == "~":
			reports.append((carry,scope,self.row,self.column))
			return
		if self.local == None: return
		typ = self.generatetype(scope)
		if typ==None: return None
		return [a.type for a in typ.args]
	self.apply(scope,head=nhead,carry=Statement([],name="U",id=0,local=0))
def possibilities(expected,scope):
	yie = []
	for local in reversed(range(len(scope.rows))):
		for id in range(len(scope.rows[local])):
			strat = scope.get(local,id)
			cont = scope.append(strat.depthpush(local+1,len(scope.rows)-local).args)
			# btype = expected.generatetype(cont);
			plain = Statement([snapshothelper(len(cont.rows),id,a) for a in strat.args],name=strat.name,id=id,local=local)
			bind = Stitching(cont)
			
			bind.compare(strat.type,expected,cont)
			# bind.compare(plain,expected,cont)
			if bind.valid:
				yie.append(strat)
	return yie

def syntaxreports(attempt,window):
	phantoms = []
	referrors = []
	typeerrors = []
	placeholders = []
	scope = Scope([])
	attempt.formalize(scope,referrors)
	for referror in referrors:
		error = '<span style="color:purple">█Unknown</span>'
		if referror[2] == 0: error = '<span style="color:red">█Mechanical Error(Argument)</span>'
		if referror[2] == 1: error = '<span style="color:#FF7F50">█Wrong name count</span>'
		if referror[2] == 2: error = '<span style="color:#FF4500">█Reference</span>'
		if referror[2] == 3: error = '<span style="color:#FF6347">█Wrong argument count</span>'
		if referror[2] == 4: continue
		pos = window.view.text_point(referror[0],referror[1])
		phantoms.append(sublime.Phantom(
			sublime.Region(pos,pos+4),
			error,
			sublime.LAYOUT_BELOW
		))
	typecheck(attempt,scope,typeerrors)
	for referror in typeerrors:
		if referror[1] != None:
			error = '<span style="color:#FFA500">█Type Error<br>'+str(referror[2])+' =/= '+str(referror[0])+' . . . \n('+str(referror[1])+')</span>'
		else:
			error = '<span style="color:#FFA500">█Mechanical Error(Type)</span>'
		pos = window.view.text_point(referror[3],referror[4])
		phantoms.append(sublime.Phantom(
			sublime.Region(pos,pos+4),
			error,
			sublime.LAYOUT_BELOW
		))
	holeanalysis(attempt,scope,placeholders)
	for report in placeholders:
		error = '<span style="color:#7FFFD4">█Hole: '+str(report[0])+'<br>'
		error = error+'<br>'.join([str(a) for a in possibilities(report[0],report[1])])+'</span>'
		pos = window.view.text_point(report[2],report[3])
		phantoms.append(sublime.Phantom(
			sublime.Region(pos,pos+4),
			error,
			sublime.LAYOUT_BELOW
		))
	return phantoms









