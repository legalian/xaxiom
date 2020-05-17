
import copy
from inspect import getfullargspec
from .lark import Lark, UnexpectedInput, Transformer, v_args, InlineTransformer, Tree
from .lark.exceptions import VisitError
import io

import hashlib
# import os.path
import os
import json
from traceback import format_stack
import re
import random
# from pycallgraph import PyCallGraph
# from pycallgraph.output import GraphvizOutput


#xax is an intrinsic type theory. There is no such thing as a normal form. there is a difference between propositional and judgemental equality. Rather than having infinite universe types, the system is wellfounded. type checking is decidable. not all things have normal forms...

dbg_haw = 0

depth = 0
len_check = re.compile('::lt::((?!::gt::).)*::gt::')
variable_check = re.compile('^\\w+$')
prefix_postfix_check = re.compile('^((\\+\\w+)|(\\w+\\+))$')

def nonhtmllength(html):
	return len(len_check.sub('',html))

if True:
	def pmultilinelist(lis,context,word):
		def ppri(sj):
			if type(sj) is not list: return context.asStr(sj)
			return context.orange("[")+",".join([ppri(k) for k in sj])+context.orange("]")
		if type(word) is not list: return context.asStr(word)
		return context.orange("|")+",".join([ppri(k) for k in word])+context.orange("|")

	def pmultilinecsv(context,trail,out,indent,lis,head,tail,lamadapt=None,callback=None,delim=",",seplist=None):
		ocontext = context
		if nonhtmllength(head)<context.magic:
			lisrepr = []
			for k in range(len(lis)):
				if lamadapt!=None:
					word = context.newcolors(lamadapt(k,lis[k]))
					if lis[k]==None:
						lisrepr.append(pmultilinelist(seplist[k],context,word))
					elif isinstance(lis[k],Tobj):
						lisrepr.append(pmultilinelist(seplist[k],context,word)+":="+lis[k].prepr(context,trail+[k]))
					else:
						lisrepr.append(lis[k].prepr(context,trail+[k],word=word))
					context = context.addbits(word)
				else: lisrepr.append(lis[k].prepr(context,trail+[k]))
			comb = delim.join(lisrepr)
			if nonhtmllength(head+comb+tail)<context.magic:
				if callback == None:
					out.append("\t"*indent+head+comb+tail)
				else:
					callback(context,out,head+comb+tail)
				return
		out.append("\t"*indent+head)
		context = ocontext
		for k in range(len(lis)):
			if lamadapt!=None:
				word = context.newcolors(lamadapt(k,lis[k]))
				if lis[k]==None:
					out.append(((indent+1)*"\t")+pmultilinelist(seplist[k],context,word)+(delim if k<len(lis)-1 else ""))
				elif isinstance(lis[k],Tobj):
					lis[k].pmultiline(context,trail+[k],out,indent+1,pmultilinelist(seplist[k],context,word)+":=",delim if k<len(lis)-1 else "")
				else:
					lis[k].pmultiline(context,trail+[k],out,indent+1,"",delim if k<len(lis)-1 else "",word=word)
				context = context.addbits(word)
			else:
				lis[k].pmultiline(context,trail+[k],out,indent+1,"",delim if k<len(lis)-1 else "")
		if callback == None:
			out.append("\t"*indent+tail)
		else:
			callback(context,out,tail)




	def firstSubObPush(iso,dok,inlen):
		while (type(iso) is int or type(iso) is Inspection) and not dok.isempty():
			if type(iso) is int:
				try:
					iso = dok.translate(iso,inlen=inlen)
				except DpushError: return None
				if type(iso) is tuple:
					inlen += iso[3].lenchange
					brok = iso[3]
					dok = iso[1]
					iso = iso[0].isSubOb()
					if type(iso) is tuple: return (brok,dok)
				else: break
			else:
				ko = iso.inspect
				try:
					iso = dok.translate(iso.root,inlen=inlen)
				except DpushError: return None
				if type(iso) is tuple:
					inlen += iso[3].lenchange
					brok = iso[3]
					dok = iso[1]
					iso = inspectref(iso[0].isSubOb(),ko)
					if type(iso) is tuple: return (brok,dok)
				else:
					iso = Inspection(iso,ko)
					break
		return None

	def isSubObPush(iso,dok,inlen):
		while (type(iso) is int or type(iso) is Inspection or type(iso) is tuple) and not dok.isempty():
			if type(iso) is int:
				iso = dok.translate(iso,inlen=inlen)
				if type(iso) is tuple:
					inlen += iso[3].lenchange
					dok = iso[1]
					iso = iso[0].isSubOb()
				else: break
			elif type(iso) is tuple:
				return tuple(isSubObPush(k,dok,inlen=inlen) for k in iso)
			else:
				ko = iso.inspect
				iso = dok.translate(iso.root,inlen=inlen)
				if type(iso) is tuple:
					inlen += iso[3].lenchange
					dok = iso[1]
					iso = inspectref(iso[0].isSubOb(),ko)
				else:
					iso = Inspection(iso,ko)
					break
		return iso


	def transferlines(self,pos):
		# if hasattr(pos,'blame'):
		# 	self.blame = pos.blame
		# else:
		# 	self.blame = format_stack()

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


	def assertstatequal(indesc,pos,one,two):
		if two != None and one != None:
			if not one.compare(two):
				raise TypeMismatch(pos,one,two,indesc)


	def prefix(si,am):
		if type(si) is list: return [prefix(s,am) for s in si]
		if si==None: return '_'
		if not variable_check.match(si): return si
		return am+si
	def postfix(si,am):
		if type(si) is list: return [postfix(s,am) for s in si]
		if si==None: return '_'
		if not variable_check.match(si): return si
		return si+am
	def generalfix(si):
		if type(si) is list: return [generalfix(s) for s in si]
		if si==None: return '_'
		return si

	def fixnames(si,ty):
		if si==None: return None
		if type(si) is list:
			if len(ty[0]) != len(si): raise InvalidSplit()
			return [fixnames(si[s],ty[0][s]) for s in range(len(si))]
		else:
			if si=='*****': return generalfix(ty[1])
			if si.endswith('*****'):	 return prefix(ty[1],si[:-5])
			if si.startswith('*****'): return postfix(ty[1],si[5:])
			return si


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
	def truncateby(jj,ss):
		if type(ss) is not list: return ss
		if type(jj) is not list: return jj
		return [truncateby(jj[s],ss[s]) for s in range(len(jj))]
	def longlist(jj):
		if type(jj) is DualSubs: return sum((longlist(k.name) for k in jj.rows),[])
		if type(jj) is list: return sum((longlist(k) for k in jj),[])
		return [jj]
	def trimlongcount(car,jj):

		return longcount(untrim(car,jj))
	def striphuman(lim,mosh):
		if type(mosh) is not list: return (lim,lim+1)
		ysu = []
		for jk in mosh:
			nan,lim = striphuman(lim,jk)
			ysu.append(nan)
		return (ysu,lim)



	def downdeepverify(ahjs,amt):
		if type(ahjs) is ScopeComplicator:
			assert ahjs.core.verdepth == amt+len(ahjs.secrets)
			for n in range(len(ahjs.secrets)):
				ahjs.secrets[n].setSafety(amt+n)
		if type(ahjs) is RefTree:
			if ahjs.src!=None: ahjs.src.setSafety(amt)
			if ahjs.args!=None: ahjs.args.setSafety(amt)
		if type(ahjs) is SubsObject:
			for j in ahjs.subs:
				if j !=None: j.setSafetyrow(amt)
		if type(ahjs) is DualSubs:
			compen = 0
			if ahjs.origin!=None: ahjs.origin[0].setSafety(amt)
			for j in ahjs.rows:
				if type(j.type) is Strategy and ahjs.verdepth==None:
					j.type.setSafety(amt+compen)
					# if j.obj!=None: j.obj.setSafety(amt+compen+longcount(j.type.args))
				else:
					j.setSafetyrow(amt+compen)
				if hasfixes(j.name): break
				compen = compen + longcount(j.name)


		if type(ahjs) is Template:
			ahjs.src.setSafety(amt)
		if type(ahjs) is Lambda:
			ahjs.obj.setSafety(amt+longcount(ahjs.si))
		if type(ahjs) is Strategy:
			ahjs.args.setSafety(amt)
			if ahjs.args.verdepth!=None: ahjs.type.setSafety(amt+longcount(ahjs.args))
	def updeepverify(ahjs):
		if type(ahjs) is ScopeComplicator:
			return ahjs.core.verdepth+len(ahjs.secrets)
		if type(ahjs) is RefTree:
			if ahjs.args!=None:
				safe = ahjs.args.getSafety()
				if safe!=None: downdeepverify(ahjs,safe)
				if ahjs.src!=None:
					safe = ahjs.src.getSafety()
					if safe!=None: downdeepverify(ahjs,safe)
				return safe
			if ahjs.src!=None:
				safe = ahjs.src.getSafety()
				if safe!=None: downdeepverify(ahjs,safe)
				return safe
		if type(ahjs) is SubsObject:

			just = None
			for j in ahjs.subs:
				if j !=None:
					just = j.getSafetyrow()
					if just != None:
						downdeepverify(ahjs,just)
						return just
		if type(ahjs) is DualSubs:
			if ahjs.origin!=None:
				downdeepverify(ahjs,ahjs.origin[0].verdepth)
				return ahjs.origin[0].verdepth
			if ahjs.verdepth==None: return
			just = None
			compen = 0
			for j in ahjs.rows:
				just = j.getSafetyrow()
				if just != None:
					downdeepverify(ahjs,just)
					return just-compen
				if hasfixes(j.name): break
				compen = compen + longcount(j.name)
		if type(ahjs) is Template:
			a = ahjs.src.getSafety()
			# if a == None: a = ahjs.subs.getSafety()
			if a != None: downdeepverify(ahjs,a)
			return a
		if type(ahjs) is Lambda:
			just = ahjs.obj.getSafety()
			if just != None: return just-longcount(ahjs.si)
		if type(ahjs) is Strategy:
			return ahjs.verdepth
			# a = ahjs.args.getSafety()
			# if a == None:
			# 	just = ahjs.type.getSafety()
			# 	if just != None: a = just - longcount(ahjs.args)
			# if a != None: downdeepverify(ahjs,a)
			# return a


	def unify(self):
		invert_op = getattr(self,"getSafety",None)
		if callable(invert_op):
			invert_op()
def _dbgEnter_detect(self,ranges):
	if isinstance(self,Tobj):
		assert not self.isfrozen()





def _dbgEnter_dpush(self,pushes,exob,frozen):
	if not frozen:
		assert not self.isfrozen()
	self.setVerified()
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
	else:
		safe = self.getSafety()
	if exob!=None:
		assert len(exob.subs)>0
		exob.setVerified()
		assert exob.verdepth<=self.getSafety()+pushes.lenchange
	if safe == None: assert False
	global dbg_haw
	if dbg_haw==0:
		pushes.objconforms(self)
	dbg_haw += 1

	# self.canbetranslated(pushes)
	# self.hascorrectlinks()

def _dbgExit_dpush(self,pushes,exob,frozen,outp):
	global dbg_haw
	dbg_haw -= 1
	if not frozen: assert not outp.isfrozen()
	pamt = pushes.lenchange
	if type(self) is TypeRow or type(self) is SubRow:
		safe = self.getSafetyrow()
		outp.setSafetyrow(None if safe == None else safe+pamt)
	else:
		safe = self.getSafety()
		outp.setSafety(None if safe == None else safe+pamt)
		outp.setVerified()
	# try:
	# outp.canbetranslated(ScopeDelta())
	# outp.hascorrectlinks()
	# except Exception as u:
	# 	print("pushed:")
	# 	print("\t",self.verdepth)
	# 	print("\t",self.prepr(FormatterObject(None,fullrepresent=False,littleeasier=False),[]))
	# 	print("\t",self.prepr(FormatterObject(None,fullrepresent=True,littleeasier=False),[]))
	# 	print("\t",pushes)
	# 	print("\t",outp.prepr(FormatterObject(None,fullrepresent=False,littleeasier=False),[]))
	# 	print("\t",outp.prepr(FormatterObject(None,fullrepresent=True,littleeasier=False),[]))
	# 	raise u


	# car = pushes.subprots(self.verdepth)

	# if hasattr(self,'alsubbedsafety'):
	# 	for j in self.alsubbedsafety:
	# 		if pushes.canTranslate(j,inlen=safe):
	# 			jah = pushes.translate(j,inlen=safe)
	# 			assert type(jah) is int
	# 			assert jah not in car
	# 			car.append(jah)

	# if outp!=self:
	# 	outp.alsubbedsafety = car
		# yama = pushes.getmemo(self,exob,False)
		# if yama == None: yama = pushes.getmemo(self,exob,True)
		# if not hasattr(yama,'alsubbedsafety'):
		# 	yama.alsubbedsafety = car
		


def _dbgEnter_pmultiline(self,context,trail,out,indent,prepend,postpend,callback):
	if context.context!=None:
		if type(self) is TypeRow or type(self) is SubRow:
			self.setSafetyrow(len(context.context))
		else:
			self.setSafety(len(context.context))
def _dbgEnter_addfibration(self,args):
	self.setVerified()
	args.setVerified()
	self.setSafety(args.getSafety()+longcount(args))
def _dbgExit_addfibration(self,args,outp):
	outp.setVerified()
	outp.setSafety(args.getSafety())
def _dbgEnter_addlambdas(self,args):
	self.setVerified()
	args.setVerified()
	self.setSafety(args.getSafety()+longcount(args))
def _dbgExit_addlambdas(self,args,outp):
	outp.setVerified()
	outp.setSafety(args.getSafety())
def _dbgEnter_emptyinst(self,limit,mog,prep):
	if prep!=None:
		prep.setVerified()
		assert prep.verdepth<=limit
def _dbgExit_emptyinst(self,limit,mog,prep,ahjs):
	limadd = limit + (longcount(self) if type(mog) is bool and mog==False else 0)
	ahjs.setVerified()
	ahjs.setSafety(limadd)
def _dbgEnter_compare(self,other,odsc,thot,extract,lefpush,rigpush):
	if extract != None:
		assert odsc != None
		for j in extract:
			if j[2]!=False:
				j[1].setSafety(odsc)
	lsum = 0 if lefpush == None else lefpush.lenchange
	rsum = 0 if rigpush == None else rigpush.lenchange
	self.setVerified()
	other.setVerified()
	if type(self) is SubRow or type(self) is TypeRow:
		other.getSafetyrow()+rsum == self.getSafetyrow()+lsum#dsc values don't match
	else:
		other.getSafety()+rsum == self.getSafety()+lsum#dsc values don't match
		if lefpush!=None: lefpush.conforms(self.getSafety())
		if rigpush!=None: rigpush.conforms(other.getSafety())
def _dbgExit_compare(self,other,odsc,thot,extract,lefpush,rigpush,ahjs):

	# print("exiting... ",ahjs,self,other)
	# assert ahjs
	if extract != None:
		assert odsc != None
def _dbgEnter_flatten(self,delta,mog,assistmog,prep,obj,fillout,then):
	assert obj == None or isinstance(obj,DelayedComplication)
	if prep != None:
		prep.setVerified()
	if obj != None:
		obj.setVerified()
		assert obj.ob.verdepth+obj.srows.lenchange<=self.verdepth+delta.lenchange
		# obj.setSafety(self.getSafety())
	if prep!=None:
		assert prep.verdepth<=self.verdepth+delta.lenchange#default to ==.
	self.setVerified()
	delta.objconforms(self)

	# self.setSafety(indesc.beginlen())#tried to flatten something not slotted for beginninglen.
def _dbgExit_flatten(self,delta,mog,assistmog,prep,obj,fillout,then,ahjs):
	if fillout == None:
		if then: ahjs,asdfasdf = ahjs
		passlen = 0 if prep==None else longcount(prep)
		ahjs.setSafety(self.getSafety()-passlen)
def _dbgEnter_verify(self,indesc,carry,reqtype,then):
	indesc.setSafety(0)
	self.setSafety(indesc.beginlen())#self is not slotted for indesc(begin) in verify
	if carry != None:
		carry.setVerified()
		carry.setSafety(len(indesc))#carry is not slotted for indesc(end) in verify

	if hasattr(self,'verdepth'): assert self.verdepth==None

	# self.hascorrectlinks()


def _dbgExit_verify(self,indesc,carry,reqtype,then,outp):

	if reqtype:
		outp,natype = outp
		natype.setSafety(len(indesc))
	elif then:
		outp,ninds = outp
		ninds.setSafety(0)
	outp.setVerified()
	outp.setSafety(len(indesc))
	if carry!=None: outp.looseconforms(carry.get_divisibility_si())
	if type(outp) is SubsObject and carry!=None:
		car = carry.asDualSubs()
		assert len(car)==len(outp.subs)

	# outp.canbetranslated(ScopeDelta())
	# outp.hascorrectlinks()
	# outp.alsubbedsafety = indesc.subprots()




class DpushError(Exception):
	pass
class OutputTooLong(Exception):
	pass
class RestartCompactify(Exception):
	def __init__(self,earlyabort):
		Exception.__init__(self,"_restart")
		self.earlyabort = earlyabort


def htmlatlocation(basepath,filename,line,col,inner):
	res = "<div style='background-color:#789F2A;border-radius:5px;margin-bottom:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>Inside File "+("UNKNOWN" if filename==None else filename)+":</div><div style='background-color:#566C27;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
	res += "File: "+basepath+("UNKNOWN" if filename==None else filename)+"<br>"
	res += "Line: "+str(line)+"<br>"
	res += "Column: "+str(col)+"<br>"
	res += inner
	res += "</div></div>"
	return res


class LanguageError(Exception):
	def __init__(self,pos,message):
		Exception.__init__(self, message)
		# self.blame = 
		self.xaxException = True
		self.file = None
		self.pos = pos
		self.message = message
		transferlines(self,pos)
		self.soft = None
		self.choices = []
		self.callpattern = None
		self.argdata = None
		self.exceptions = None
		self.root = None
	def htmlformat(self,struct,trail,context,prepend,postpend="",tabs=0,forbidrange=None,additional = None):
		a = []
		fo = FormatterObject(context,forhtml=True,forbidrange=forbidrange,fullrepresent=False,exceptions=self.exceptions)
		if additional!=None:
			fo = fo.addbits(fo.newcolors(additional))
		try:
			struct.pmultiline(fo,(self.root if self.root!=None else [])+trail,a,tabs,prepend,postpend)
		except OutputTooLong:
			a.append("...")
		return "<br>".join([j.replace("&","&amp;").replace("\t","&nbsp;&nbsp;&nbsp;&nbsp;").replace("<","&lt;").replace(">","&gt;").replace("::lt::","<").replace("::gt::",">") for j in a])
	def setupstream(self,parent,ind):
		self.root = (parent.root if parent.root!=None else [])+[ind]
		self.exceptions = parent.exceptions


	def setfile(self,file):
		self.file = file
		return self
	def innermessage(self):
		return self.message
	def name(self):
		return "Language Error"
	def hiddenrange(self):
		return ScopeDelta([] if self.argdata==None else [(-self.argdata[2],len(self.argdata[4])-self.argdata[2])])
	def paramhtml(self):
		# def namefromSI(si,car,trail): repr(yoks)+"<br>"+repr(trail)+
		# 	if type(si) is not list:
		yoks,trail,lentho,rowtype,context = self.argdata
		trimmy = context.trimabsolute(lentho)
		message = "<div style='background-color:#4F99A5;border-radius:5px;margin-bottom:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>Inside Parameter "+repr(trail)+":</div><div style='background-color:#39595B;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
		s = 0
		for yok in sorted(yoks,key=lambda x:x[0]):
			if yok[2]==False:
				message += self.htmlformat(yok[1],[s],trimmy.acceptedlist(),str(yok[0])+" = ")+"<br>"
			else:
				message += self.htmlformat(yok[1],[s],trimmy,str(yok[0])+" = ")+"<br>"
			s+=1
			if type(yok[2]) is not bool:
				message += "<div style='background-color:#426d70'>"+self.htmlformat(yok[2],[s],trimmy,"Computed type:",tabs=1)+"</div>"
				s+=1
			if len(yok)>3: message += "<div style='background-color:#426d70'>&nbsp;&nbsp;&nbsp;&nbsp;(assumed from "+str(yok[3])+" parameter.)</div>"
		if rowtype!=None: message += self.htmlformat(rowtype,[s],context,"Expected Type: ",forbidrange=ScopeDelta([(-lentho,len(context)-lentho)]))
		return message + "</div></div>"
		# return message
	def errorhtml(self):
		message = ""
		if self.argdata!=None: message+=self.paramhtml()
		message += "<div style='background-color:#9A274E;border-radius:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>"+self.name()+":</div><div style='background-color:#612839;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
		message += self.innermessage()
		return message + "</div></div>"
	def tohtml(self):
		choices = []
		callpattern = None

		# encounter = {}
		for choice in range(len(self.choices)):
			name,row,indesc,error = self.choices[choice]
			pushedrow = row.observeAT(len(indesc))
			# pushedrow = row.simpush(SimpleDelta(len(indesc)-cr,   min(cr,len(indesc))  ))
			formatted = self.htmlformat(pushedrow,[choice],indesc,name+":")
			for subch in range(len(choices)):
				if choices[subch][0].compare(pushedrow):
					if nonhtmllength(formatted)<nonhtmllength(choices[subch][1]):
						choices[subch] = (pushedrow,formatted,error)
					break
			else:
				if choice==self.callpattern: callpattern = len(choices)
				choices.append((pushedrow,formatted,error))

		message = ""
		for choice in range(len(choices)):
			if choice == callpattern: continue
			discard,msg,err = choices[choice]
			err.setupstream(self,len(self.choices)+choice)
			message += "<div style='background-color:#8969C3;border-radius:5px;margin-bottom:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>Alternate interpretation:</div><div style='background-color:#594973;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
			message += msg
			if err==None:
				message += "<div>Possibility not considered; parameters matched earlier possibility already.</div>"
			else:
				message += "<div>Disregarded Because:</div>"
				message += err.errorhtml()
			message += "</div></div>"
		if callpattern != None:
			message += "<div style='background-color:#4F99A5;border-radius:5px;margin-bottom:5px;'><div style='color:#282923;margin-left:10px;margin-right:10px'>Inside function call:</div><div style='background-color:#39595B;padding:10px;border-bottom-right-radius:5px;border-bottom-left-radius:5px;'>"
			message += choices[callpattern][1]
			message += "</div></div>"
		message += self.errorhtml()
		return message
	def soften(self,shouldsoft):
		self.soft = shouldsoft
		return self
	def callingcontext(self,choices,thispattern):
		if self.callpattern!=None: return self
		self.callpattern = thispattern
		self.choices = choices
		return self
	def addparameterdata(self,yoks,trail,lentho,rowtype,context):
		# def _dbgEnter():
		# 	for yok in yoks:

		if self.callpattern==None and self.argdata!=None: return self
		if self.argdata==None and self.callpattern==None:
			self.argdata = (yoks,trail,lentho,rowtype,context)
		return self
	def callback(self,backwards):
		def wrap(dat):
			jar = tuple(int(a) for a in dat[1:-1].split(','))
			print(jar)
			if self.exceptions==None: self.exceptions = set()
			else: self.exceptions = set(a for a in self.exceptions if len(a)<=len(jar) or a[:len(jar)]!=jar)
			if jar in self.exceptions: self.exceptions.remove(jar)
			else: self.exceptions.add(jar)
			backwards()
		return wrap

class NonUnionTypeError(LanguageError):
	def __init__(self,pos,expected,context):
		LanguageError.__init__(self,pos,"Objects of the form (a,b) must only be supplied to types of the form {A,B}.")
		self.expected=expected
		self.context=context
	def innermessage(self):
		return self.message+"<br>"+self.htmlformat(self.expected,[],self.context,"Expected type: ",forbidrange=self.hiddenrange())
	def name(self):
		return "Type mismatch error"
class NonLambdaTypeError(LanguageError):
	def __init__(self,pos,expected,context):
		LanguageError.__init__(self,pos,"Objects of the form |c|d must only be supplied to types of the form [C]D.")
		self.expected=expected
		self.context=context
	def innermessage(self):
		return self.message+"<br>"+self.htmlformat(self.expected,[],self.context,"Expected type: ",forbidrange=self.hiddenrange())
	def name(self):
		return "Type mismatch error"
class TypeRequiredError(LanguageError):
	def __init__(self,pos,lam):
		LanguageError.__init__(self,pos,"Objects of the form "+("|c|d" if lam else "(a,b)")+" require an expected type.")
	def name(self):
		return "Type assumption error"
class TypeMismatch(LanguageError):
	def __init__(self,pos,expected,got,context):
		LanguageError.__init__(self,pos,"Type mismatch.")
		self.expected=expected
		self.got=got
		self.context=context
		self.adfb=None
	def innermessage(self):
		res =  self.htmlformat(self.expected,[0],self.context,"Expected: ",forbidrange=self.hiddenrange())
		res += "<br>"
		res += self.htmlformat(self.got,[1],self.context,"Provided: ",forbidrange=self.hiddenrange())
		if self.adfb!=None:
			if self.adfb[0]==None or self.adfb[1]==None:
				res += "<br>Common inheritance ancestor found, but casting could not find an analagous component to this:"
			else:
				res += "<br>Common inheritance ancestor found, but implicit casting failed on this comparison: "
			if self.adfb[0]==None:
				res += "<br>Expected side: { absent }"
			else:
				res += "<br>"+self.htmlformat(self.adfb[0],[2],self.context,"Expected side: ",forbidrange=self.hiddenrange(),additional=self.adfb[2])
			if self.adfb[1]==None:
				res += "<br>Provided side: { absent }"
			else:
				res += "<br>"+self.htmlformat(self.adfb[1],[3],self.context,"Provided side: ",forbidrange=self.hiddenrange(),additional=self.adfb[3])
		return res
	def name(self):
		return "Type mismatch"
	def ihfb(self,ihfb):
		self.adfb=ihfb
		return self

class ObjectMismatch(LanguageError):
	def __init__(self,pos,expected,got,context):
		LanguageError.__init__(self,pos,"Object mismatch.")
		self.expected=expected
		self.got=got
		self.context=context
	def innermessage(self):
		res = "Templating could not resolve the expected object so that it is equivalent to the provided one.<br>"
		res += self.htmlformat(self.expected,[0],self.context,"Expected: ",forbidrange=self.hiddenrange())
		res += "<br>"
		res += self.htmlformat(self.got,[1],self.context,"Provided: ",forbidrange=self.hiddenrange())
		return res
	def name(self):
		return "Object mismatch"

class InvalidSplit(LanguageError):
	def __init__(self):
		LanguageError.__init__(self,None,"Invalid split pattern.")
	def reblame(self,pos,tt,si,context):
		LanguageError.__init__(self,pos,"Invalid split pattern.")
		self.si = repr(si)
		self.tt = tt
		self.context=context
		return self
	def innermessage(self):
		return "Pattern: "+self.si+"<br>"+self.htmlformat(self.tt,[],self.context,"Tried to split: ",forbidrange=self.hiddenrange())
	def name(self):
		return "Invalid split pattern"
class CouldNotDeduceType(LanguageError):
	def __init__(self,pos):
		LanguageError.__init__(self,pos,"Could not deduce type of argument.")
	def name(self):
		return "Type assumption error"
class VariableAssignmentError(LanguageError):
	def __init__(self,pos,name):
		LanguageError.__init__(self,pos,"Too many positional arguments" if name==None else "Unexpected keyword argument: " + str(name))
	def name(self):
		return "Unexpected argument"




# RRR = 0

# class DelayedSub:
# 	def __init__(self,core,isSubOb):
# 		self.core = core
# 		# self.isSubOb = isSubOb
# 		# self.rows = ScopeDelta() if rows==None else rows
# 		self.memo = {}
# 		# def _dbgTest():
# 		# 	self.rows.objconforms(self.core)
# 		# 	global RRR
# 		# 	RRR+=1
# 		# 	if RRR==1:
# 		# 		if self.core.detect(self.rows):
# 		# 			print("-=-=-=--=-==-=-=-=-=")
# 		# 			print(self.core)
# 		# 			print(self.rows)
# 		# 			assert False
# 		# 	RRR-=1

# 		# 	assert isSubObPush(self.core.isSubOb(),self.rows,self.core.verdepth) == self.isSubOb



# 	def dpush_ds(self,rows,myname):
# 		if rows.isempty(): return self
# 		if self.rows.isempty(): ko = rows
# 		else: ko = self.rows+rows

# 		# ko.tampdown()
# 		if rows.islowerboundRev(myname): return self
# 			# return DelayedSub(self.core,isSubObPush(self.isSubOb,rows,inlen=self.core.verdepth+self.rows.lenchange),ko)
# 		# print(self.core.)
# 		# if len(ko.pushes)==1 and len(ko.pushes[0])==2 and ko.pushes[0][0]>=0:
# 		# 	debugg = self.core.simpush(SimpleDelta(ko.pushes[0][0],ko.pushes[0][1]))
# 		# else:
# 		debugg = self.core.dpush(ko)
# 		return DelayedSub(debugg,debugg.isSubOb())
# 	def verdepth(self):
# 		return self.core.verdepth+self.rows.lenchange



# need to write unwrappers



# the cure- six different ways

	# there are more memos...

	# the most important one: <><>
	# the least important one: tm


# need to ensure that objects all have the same delayedsub.
# on load you can do better w this.
# on verify you can also do better w this.
# mergedeltas will also help.


def alreadycanbetranslated(self,pushes,cobt=set()):
	# return True
	# hashpushes = tuple(sorted(pushes.subprots()))
	# if hashpushes == tuple([]): return True
	# if (self,hashpushes) in cobt:
		# print("already discovered")
		# return True
	# cobt.add((self,hashpushes))
	return False


class ScopeDelta:
	def __hash__(self):
		# try:
		return hash(tuple(tuple(a[0]) if len(a)==1 else (a[0],a[1],tuple(a[2])) if len(a)==3 else a for a in self.pushes))
		# except:
		# 	print(self.pushes)
		# 	assert False
	def __eq__(self,other):
		return type(other) is ScopeDelta and self.pushes == other.pushes

	def tampdown(self):
		# while len(self.pushes)>1 and len(self.pushes[-1])==2 and len(self.pushes[-2])==2:
		# 	a,b = self.pushes[-2]
		# 	c,d = self.pushes[-1]
		# 	if a>=0 and a+b>=d:
		# 		if b<=d and c>=0:
		# 			del self.pushes[-1]
		# 			self.pushes[-1] = (a+c,b)
		# 			continue
		# 		elif c+d>=a+b and c<=0:
		# 			del self.pushes[-1]
		# 			if a+c==0: del self.pushes[-1]
		# 			else: self.pushes[-1]=(a+c,min(b,d))
		# 			continue
		# 	break
		pass

	# def isolate(self)


		# do the memo thing for gy[2]
		# then dual memo

	def __init__(self,pushes=None):
		self.pushes = pushes if pushes !=None else []
		self.lenchange = sum(j[0] if len(j)==2 else j[0]+len(j[2]) for j in self.pushes if len(j)==2 or len(j)==3)
		def _dbgTest():
			for j in self.pushes:
				if len(j)==2:
					assert type(j[0]) is int
					assert type(j[1]) is int
					assert j[0]!=0
				elif len(j)==4:
					assert type(j[0]) is int
					assert type(j[1]) is int
					assert type(j[2]) is int
					assert type(j[3]) is int
					assert j[0]+j[1]!=j[2]+j[3] and j[0]!=j[2]
				elif len(j)==3:
					assert type(j[0]) is int
					assert type(j[1]) is int
					assert type(j[2]) is list
					assert j[0]!=0
				else:
					if type(j[0]) is not list:
						print(j)
						assert False
					assert len(j[0])!=0
					for key,symbol in j[0]:#insert subtags for dbg
						if symbol!=None: assert symbol.verdepth<=key

	def memoizeGet(self,pushes,key,core):
		if hasattr(self,'delaymemo'):
			whomd = self.delaymemo.get(key)
			if whomd!=None: return whomd
		else: self.delaymemo = {}
		whomd = core if pushes.islowerboundRev(key) else core.dpush(pushes)
		self.delaymemo[key] = whomd
		return whomd
		# def _dbgTest():
		# 	kaka = whomd.isSubOb()
		# 	if type(kaka) is int: assert kaka<key
		# 	if type(kaka) is Inspection: assert kaka.root<key

	def getmemo(self,input,exob,frozen):
		fef = input.verdepth+self.lenchange
		if hasattr(self,'dpm'):
			whomd = self.dpm.get((input,exob))
			if whomd!=None:
				early = whomd.get(fef)
				if early==None:
					vov,early = next(iter(whomd.items()))
					early = early.simpush(SimpleDelta(fef-vov,min(vov,fef)))
					whomd[fef] = early
				return early
		else: self.dpm = {}
		if frozen:
			if hasattr(self,'dfm'):
				whomd = self.dfm.get((input,exob))
				if whomd!=None:
					early = whomd.get(fef)
					if early==None:
						vov,early = next(iter(whomd.items()))
						early = early.simpush(SimpleDelta(fef-vov,min(vov,fef)))
						whomd[fef] = early
					return early
			else: self.dfm = {}
		return None


	def setmemo(self,input,exob,frozen,output):
		if frozen and output.isfrozen():
			self.dfm[(input,exob)] = {input.verdepth+self.lenchange:output}
		else:
			self.dpm[(input,exob)] = {input.verdepth+self.lenchange:output}


	def __add__(self,other):


		if len(other.pushes)==0: return self
		ko = ScopeDelta(self.pushes+other.pushes)
		def _dbgTest():
			try:
				a = self.subprots()
				b = other.subprots()+[]
				for u in a:
					if not other.canTranslate(u,ignoresubs=True): continue
					c = other.translate(u,ignoresubs=True)
					assert c not in b
					b.append(c)
				ko.memoSBP = b
			except Exception as u:
				print(ko)
				raise u

		if hasattr(other,'delaymemo'): ko.delaymemo = other.delaymemo
		return ko
	def __sub__(self,other):
		return self+(-other)
	def __neg__(self):
		res = []
		for j in reversed(self.pushes):
			if len(j)==2:
				res.append((-j[0],j[1]))
			elif len(j)==4:
				res.append((j[0],j[3],j[2]+j[3]-j[1],j[1]))
			else: assert False
		return ScopeDelta(res)
	def __repr__(self):
		return repr(self.pushes)
	def objconforms(self,obj):
		safe = obj.verdepth
		self.conforms(safe)
		# obj.canbetranslated(self)
		# if hasattr(obj,'alsubbedsafety'):
		# 	car = self.subprots(safe)
		# 	for j in obj.alsubbedsafety:
		# 		if self.canTranslate(j,inlen=safe):
		# 			jah = self.translate(j,inlen=safe)
		# 			if type(jah) is not int:
		# 				print("already subbed but resubbed:",j)
		# 				print(self)
		# 				assert False
		# 			assert jah not in car
		# 			car.append(jah)
	def conforms(self,safe):
		# if hasattr(self,'confd'):
		# 	if safe in self.confd: return
		# else: self.confd = set()
		# self.confd.add(safe)
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==2:
				assert j[1]<=safe
				assert j[1]-j[0]<=safe
				safe+=j[0]
				assert type(j[0]) is int
				assert type(j[1]) is int
			elif len(j)==4:
				assert j[0]>=0
				assert j[1]>=0
				assert j[2]>=0
				assert j[3]>=0
				assert j[0]+j[1]<=j[2]
				assert j[2]+j[3]<=safe
				assert type(j[0]) is int
				assert type(j[1]) is int
				assert type(j[2]) is int
				assert type(j[3]) is int
			elif len(j)==3:
				assert j[1]<=safe
				assert j[1]-j[0]<=safe
				safe+=j[0]+len(j[2])
				assert type(j[0]) is int
				assert type(j[1]) is int
				assert type(j[2]) is list
			else:
				assert type(j[0]) is list
				for key,symbol in j[0]:#insert subtags for dbg
					if symbol==None: continue
					assert key<safe
					if symbol.verdepth>key:
						assert symbol.verdepth<=key
					# trans = ScopeDelta([(safe-symbol.verdepth,symbol.verdepth)]+self.pushes[i+1:])

					trans = ScopeDelta(self.pushes[i+1:])
					# symbol.canbetranslated(ScopeDelta([(safe-symbol.verdepth,symbol.verdepth)]+self.pushes[i+1:]))

					if trans.canTranslate(key,inlen=safe):
						if type(trans.translate(key,inlen=safe)) is not int:
							print("breka")
							print()
							print(self)
							print()
							assert False

					# assert symbol.verdepth>key
					# assert not symbol.detect(ScopeDelta([(symbol.verdepth-key,key)]))

	def isolate(self):
		return ScopeDelta(copy.copy(self.pushes))
	def isempty(self):
		return len(self.pushes)==0
	def append(self,j):
		self.pushes.append(j)
		if len(j)==2 or len(j)==3: self.lenchange += j[0] if len(j)==2 else j[0]+len(j[2])
		if hasattr(self,'tm'): self.tm = {}
		if hasattr(self,'dpm'): self.dpm = {}
		if hasattr(self,'dfm'): self.dfm = {}
	def islowerbound(self,fug):
		for j in self.pushes:
			if len(j)==2:
				if fug>j[1]:
					if j[0]<0: return False
					fug+=j[0]
			elif len(j)==4:
				if   fug>j[0]: fug = max(fug,j[2]+j[3])
			elif len(j)==3:
				if fug>=j[1]:
					return False
		return True
	def islowerboundRev(self,fug):
		# return False
		for j in reversed(self.pushes):
			if len(j)==2:
				if fug>=j[1]:
					return 
					if j[0]<0: return False
					if fug>j[0]+j[1]: return False
					fug-=j[0]
					if fug!=j[1]:
						print(self,fug)
						assert False
			elif len(j)==4:
				if   fug>=j[0]:
					return False
					fug = max(fug,j[2]+j[3])
			elif len(j)==3:
				if fug>=j[1]:
					return False
			else:
				for key,symbol in j[0]:
					if fug>key: return False
		return True


		# symbol.verdepth <= key
			# key is above you: key wont be hit.
			# key is beneath you: it'll sub out but the resultant stuff will all be beneath you anyway, so you continue onwards.

	# def breakdown(self):

	def subprots(self):
		if hasattr(self,'memoSBP'): return self.memoSBP
		hama = []
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==1:
				for key,symbol in j[0]:#insert subtags for dbg
					trans = ScopeDelta(self.pushes[i+1:])
					if trans.canTranslate(key):
						hama.append(trans.translate(key))
		for a in range(len(hama)):
			for b in range(a):
				assert hama[a]!=hama[b]
		self.memoSBP = hama
		return hama
	def canTranslate(self,fug,inlen=None,ignoresubs=False):
		changefar = 0
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==2:
				changefar += j[0]
				if fug>=j[1]:
					fug+=j[0]
					if fug<j[1]: return False
			elif len(j)==4:
				if   fug>=j[0] and fug<j[0]+j[1]: fug+=j[2]+j[3]-j[0]-j[1]
				elif fug>=j[2] and fug<j[2]+j[3]: fug+=j[0]-j[2]
				elif fug>=j[0]+j[1] and fug<j[2]: fug+=j[3]-j[1]
			elif len(j)==3:
				changefar += j[0]+len(j[2])
				if fug>=j[1]:
					if fug+j[0]<j[1]: return False
					fug+=j[0]+len(j[2])
			elif not ignoresubs:
				for key,symbol in j[0]:#insert subtags for dbg
					if fug==key:
						if symbol==None: return False
						trans = ScopeDelta([(inlen+changefar-symbol.verdepth,symbol.verdepth)]+self.pushes[i+1:])
						return trans.islowerbound(key) or not symbol.detect(trans)
						# return symbol.detect(trans)
		return True
	def translate(self,fug,inlen=None,ignoresubs=False):
		if not hasattr(self,'tm'): self.tm = {}
		# else:
		# 	dtry = self.tm.get(fug)
		# 	if dtry!=None:
		# 		if type(dtry) is dict:
		# 			further = dtry.get(inlen)
		# 			if further != None: return further
		# 			tlen,further = next(iter(dtry.items()))
		# 			if len(further)==3:
		# 				further = (further[0],ScopeDelta(further[1].pushes[:-1]+[(further[1].pushes[-1][0]+tlen-inlen,further[1].pushes[-1][1])]),further[2])
		# 			else:
		# 				further = (further[0],ScopeDelta([(further[1].pushes[0][0]+inlen-tlen,further[1].pushes[0][1])]+further[1].pushes[1:]),further[2])
		# 			dtry[inlen]=further
		# 			return further
		# 		return dtry
		ifug = fug
		changefar = 0
		for i in range(len(self.pushes)):
			j = self.pushes[i]
			if len(j)==2:
				changefar += j[0]
				if fug>=j[1]:
					fug+=j[0]
					if fug<j[1]: raise DpushError()
			elif len(j)==4:
				if   fug>=j[0] and fug<j[0]+j[1]: fug+=j[2]+j[3]-j[0]-j[1]
				elif fug>=j[2] and fug<j[2]+j[3]: fug+=j[0]-j[2]
				elif fug>=j[0]+j[1] and fug<j[2]: fug+=j[3]-j[1]
			elif len(j)==3:
				if fug>=j[1]:
					if fug+j[0]<j[1]:
						fug = (j[2],ScopeDelta(self.pushes[:i] if j[2][0].verdepth==(inlen+changefar) else self.pushes[:i]+[(j[2][0].verdepth-(inlen+changefar),j[2][0].verdepth)]),ScopeDelta(self.pushes[i+1:]))
						self.tm[ifug]={inlen:fug}
						return fug
					fug+=j[0]+len(j[2])
				changefar += j[0]+len(j[2])
			elif not ignoresubs:
				for key,symbol in j[0]:#insert subtags for dbg
					if fug==key:
						if symbol==None: raise DpushError
						for w in self.pushes[i+1:]:
							if len(w)==2:
								if fug>=w[1]:
									fug+=w[0]
									if fug<w[1]:
										fug = (symbol,ScopeDelta(self.pushes[i+1:] if inlen+changefar==symbol.verdepth else [(inlen+changefar-symbol.verdepth,symbol.verdepth)]+self.pushes[i+1:]),None,ScopeDelta(self.pushes[:i+1]))
										break
							elif len(w)==4:
								if   fug>=w[0] and fug<w[0]+w[1]: fug+=w[2]+w[3]-w[0]-w[1]
								elif fug>=w[2] and fug<w[2]+w[3]: fug+=w[0]-w[2]
								elif fug>=w[0]+w[1] and fug<w[2]: fug+=w[3]-w[1]
						else:
							fug = (symbol,ScopeDelta(self.pushes[i+1:] if inlen+changefar==symbol.verdepth else [(inlen+changefar-symbol.verdepth,symbol.verdepth)]+self.pushes[i+1:]),fug,ScopeDelta(self.pushes[:i+1]))
						if hasattr(self,'delaymemo'): fug[1].delaymemo = self.delaymemo
						# if not hasattr(self,'isdr'): self.isdr = {}
						# mod = self.isdr.get(i)
						# if mod==None:
						# 	mod = ScopeDelta(self.pushes[i+1:])
						# 	self.isdr[i] = mod
						# assert changefar+ScopeDelta(self.pushes[:i+1]).lenchange == self.lenchange
						self.tm[ifug]={inlen:fug}
						return fug 
		self.tm[ifug]=fug
		return fug
	def subset(self,fug):
		track = []
		for j in self.pushes:
			assert len(j)==2#safemode
			if fug>j[1]:
				track.append(j)
				fug+=j[0]
				assert fug>=j[1]#safemode
		return ScopeDelta(track)
	def gentlesubset(self,fug):
		track = []
		for j in self.pushes:
			assert j[0]<=0#safemode
			assert len(j)==2#safemode
			if fug>=j[1]-j[0]: track.append(j)
			if fug>=j[1]: fug = max(fug+j[0],j[1])
		return ScopeDelta(track)


	def translateGentle(self,fug):
		return self.gentlesubset(fug).translate(fug)
	# def lenchange(self):
	# 	return sum(j[0] if len(j)==2 else j[0]+len(j[2]) for j in self.pushes if len(j)==2 or len(j)==3)

class FormatterObject:
	def __init__(self,context,magic=60,forhtml=False,forbidrange=None,littleeasier=True,colormap=None,fullrepresent=False,printcomplicators=True,exceptions=None):
		self.magic = magic
		self.context = context.flatnamespace() if type(context) is ScopeObject else context
		self.forhtml = forhtml
		self.forbiddenrange = (forbidrange if forbidrange!=None else ScopeDelta()) - (context.prepushes+context.postpushes if type(context) is ScopeObject else ScopeDelta([]))#[] if forbidrange==None else forbidrange
		self.littleeasier = littleeasier
		self.colormap = {} if colormap==None else colormap
		self.fullrepresent = fullrepresent
		self.printcomplicators = printcomplicators
		self.exceptions = set() if exceptions==None else exceptions

	def getname(self,name):
		if type(name) is str:
			if self.forhtml: return "::lt::span style='color:#fdee73'::gt::"+name+"::lt::/span::gt::"
			return name
		if self.context == None: return str(name)
		if type(name) is int:
			if name in self.colormap and self.forhtml:
				return "::lt::span style='color:"+self.colormap[name]+"'::gt::"+("{no name}" if self.context[name]==None else self.context[name])+"::lt::/span::gt::"
			if len(self.context)==0: return "{uni"+"verse}"
			return self.context[name]
	def clickable(self,trail):
		if not self.forhtml: return ""
		# return "::lt::a href='"+str(trail)+"'::gt::::lt::span style='color:#FFF;background-color:#FFFFFF55;border-radius:25%;padding: -.25em .5em -.25em .5em;' ::gt::+::lt::/span::gt::::lt::/a::gt::"
		return "::lt::a href='"+str(trail)+"' style='color:#FFF;background-color:#FFFFFF55;border-radius:25%;padding: -.25em .5em -.25em .5em;' ::gt::+::lt::/a::gt::"
	def makeclickable(self,content,trail):
		if not self.forhtml: return content
		# return "::lt::a href='"+str(trail)+"'::gt::::lt::span style='color:#FFF;background-color:#FFFFFF55;border-radius:25%;padding: -.25em .5em -.25em .5em;' ::gt::+::lt::/span::gt::::lt::/a::gt::"
		return "::lt::a color=#FFF href='"+str(trail)+"'::gt::"+content+"::lt::/a::gt::"
	def shouldunwrap(self,name,trail):
		if not self.forbiddenrange.canTranslate(name): return True
		if tuple(trail) in self.exceptions: return not self.fullrepresent
		return self.fullrepresent
	def shouldtrim(self,trail):
		if tuple(trail) in self.exceptions: return not self.littleeasier
		return self.littleeasier

	def red(self,inp):
		if self.forhtml: return "::lt::span style='color:#F92672'::gt::"+inp+"::lt::/span::gt::"
		return inp
	def orange(self,inp):
		if self.forhtml: return "::lt::span style='color:#FD971F'::gt::"+inp+"::lt::/span::gt::"
		return inp
	def addbits(self,nb):
		if self.context==None: return self
		def allbits(bit,canc):
			if type(bit) is list:
				res = []
				for b in bit:
					j,canc = allbits(b,canc)
					res = res+j
				return (res,canc)
			return ([(bit[0],bit[1],canc)],canc+1)
		newbits = allbits(nb,len(self.context))[0]
		return FormatterObject(
			self.context+[k[0] for k in newbits],
			magic=self.magic,
			forhtml=self.forhtml,
			forbidrange=self.forbiddenrange,
			littleeasier=self.littleeasier,
			colormap=dict([kv for kv in list(self.colormap.items())+[(index,color) for name,color,index in newbits]]),
			fullrepresent=self.fullrepresent,
			printcomplicators=self.printcomplicators,
			exceptions=self.exceptions
		)
	def asStr(self,word):
		if self.forhtml:
			if word[1]==None: return str(word[0])
			return "::lt::span style='color:"+word[1]+"'::gt::"+str(word[0])+"::lt::/span::gt::"
		else: return str(word[0])

	# def striphuman(lim,mosh):
	# 	if type(mosh) is not list: return (lim,lim+1)
	# 	ysu = []
	# 	for jk in mosh:
	# 		nan,lim = striphuman(lim,jk)
	# 		ysu.append(nan)
	# 	return (ysu,lim)

	def randomcolor(self):
		def hsv_to_rgb(h, s, v):
			if s == 0.0: return (v, v, v)
			i = int(h*6.) # XXX assume int() truncates!
			f = (h*6.)-i; p,q,t = v*(1.-s), v*(1.-s*f), v*(1.-s*(1.-f)); i%=6
			if i == 0: return (v, t, p)
			if i == 1: return (q, v, p)
			if i == 2: return (p, v, t)
			if i == 3: return (p, q, v)
			if i == 4: return (t, p, v)
			if i == 5: return (v, p, q)
		def clamp(x): 
			return max(0, min(int(x*255), 255))
		r,g,b = hsv_to_rgb(random.uniform(80/360.0,280.0/360.0),.7,1)
		return "#{0:02x}{1:02x}{2:02x}".format(clamp(r),clamp(g),clamp(b))
		


	def newcolors(self,si):
		def allbits(si):
			if type(si) is list: return [allbits(b) for b in si]
			# assert si==None or type(si) is str
			return (si,self.randomcolor())
		return allbits(si)

def compose(mapone,maptwo):
	if type(mapone) is list: return [compose(i,maptwo) for i in mapone]
	return maptwo[mapone]
def noneiflatten(map):
	if type(map) is list: return [noneiflatten(m) for m in map]
	return None

def buildfrom(si,plat,vdp,names):
	def _dbgEnter():
		def recurse(s):
			if type(s) is not list:
				assert s<len(plat) and plat[s]!=None
			else:
				for r in s: recurse(r)
		recurse(si)
	if type(si) is list:
		return SubsObject([SubRow(None,buildfrom(m,plat,vdp,names)) for m in si],verdepth=vdp)
	else:
		return entrycomplicate(plat[si].observe(),plat[:si],names=names[:si])

def inR(si,val):
	if type(si) is list: return any(inR(s,val) for s in si)
	return val==si

def extfind(h,si,lc=0):
	if type(si) is list:
		for k in si:
			u,lc = extfind(h,k,lc)
			if u!=None: return (u,None)
		return (None,lc)
	if si==h: return (lc,None)
	return (None,lc+1)

# class MalformedInheritancePath(Exception):
# 	def __init__(self,index):
# 		Exception.__init__(self,"_malformedInheritance")
# 		self.index = index


class MalformedInheritancePath(Exception):
	def __init__(self,ihfb):
		Exception.__init__(self,"_malformedInheritance")
		self.ihfb = ihfb

# def psuedoDpush(si,pushes,h=None):
# 	if type(si) is list: return [psuedoDpush(si[s],pushes,h=h if h!=None else s) for s in range(len(si))]
# 	for push in reversed(pushes):
# 		if si == push: raise MalformedInheritancePath(h)
# 		if si > push: si = si-1
# 	return si

def reparent(provided,pA,provob):
	def trimout(map,car):
		if type(map) is not list: return map
		assert len(map)==len(car)
		return [trimout(map[s],car[s]) for s in range(len(map)) if car[s]!=False]

	if pA==0: return provob
	dualprovided,dp_secrets,dp_names = provided.diveIntoDualSubs()

	pp,obk,upgradesPrime = dualprovided.origin
	upgrades = {up:1 for up in upgradesPrime}
	pp,gok,goknames = pp.diveIntoDualSubs()
	# for y in reversed(pp.erased): del obk[y]
	p=1
	while p<pA:
		pp,obi,upgradesPrime = pp.origin
		pp,trash,trashnames = pp.diveIntoDualSubs()
		gok = gok+trash
		goknames = goknames+trashnames
		nup = {}
		canmerge = True
		for k,v in upgrades.items():
			for i in range(len(obi)):
				if obk[i]==k:
					nup[i] = v
					canmerge = False
					break
		if not canmerge: break
		for j in upgradesPrime: nup[j] = nup.get(j,0)+1
		upgrades = nup
		obk = compose(obi,obk)
		p+=1

	assert type(upgrades) is dict
	if len(dp_secrets):
		tar = dualprovided.inheritpopulate(trimout(obk,pp.get_divisibility_si()),provob.simpush(SimpleDelta(len(dp_secrets),provob.verdepth)),obk,upgrades)
	else:
		tar = dualprovided.inheritpopulate(trimout(obk,pp.get_divisibility_si()),provob,obk,upgrades)

	def _dbgTest():
		print()
		print(pA,p)
		print(upgrades)
		tar.looseconforms(pp.get_divisibility_si())
	if pA-p==0: return entrycomplicate(tar,dp_secrets,names=dp_names)
	assert False
	return entrycomplicate(reparent(entrycomplicate(pp,gok,names=goknames),pA-p,tar),dp_secrets,names=dp_names)

def downparent(expected,headE,eA,provob,extract=None,thot=None,odsc=None,owner=None):
	def _dbgEnter():
		provob.looseconforms(headE.get_divisibility_si())
	def _dbgExit(outp):
		outp.looseconforms(expected.get_divisibility_si())

	if eA==0: return provob


	dualexpected = expected.asDualSubs()

	pp,obk,upgradesPrime = dualexpected.origin
	upgrades = {up:1 for up in upgradesPrime}
	pp = pp.asDualSubs()

	for e in range(1,eA):
		pp,obi,upgradesPrime = pp.origin
		pp = pp.asDualSubs()
		nup = {}
		canmerge = True
		for k,v in upgrades.items():
			for i in range(len(obi)):
				if obk[i]==k:
					nup[i] = v
					canmerge = False
					break
		if not canmerge:
			raise LanguageError(None,"Inheritance this complicated has not been thoroughly tested yet.")
			# return downparent(,,,downparent())
		for j in upgradesPrime: nup[j] = nup.get(j,0)+1
		upgrades = nup
		obk = compose(obi,obk)

	guflat = headE.flatten(ScopeDelta([]),noneiflatten(obk),obj=DelayedComplication(provob))
	
	finob = []


	moat = ScopeDelta()

	# vvleft = 0

	cusecrets = []
	cunames = []

	for h in range(len(dualexpected.rows)):
		fou = extfind(h,obk)[0]
		if dualexpected.rows[h].obj!=None:
			cusecrets = cusecrets + dualexpected.rows[h].ripsingle()
			cunames = cunames + longlist(dualexpected.rows[h].name)
			continue

		if fou==None:
			raise MalformedInheritancePath((dualexpected.rows[h],None,[a.name for a in dualexpected.rows[:h]],None))

		vv = longcount(dualexpected.rows[h].name)

		moka = guflat.flat[fou].observe()

		compObs   = [a.obj for a in guflat.flat[:fou]]
		compNames = [a.name for a in guflat.flat[:fou]]

		inquestion     = entrycomplicate(moka.obj, compObs,names=compNames)
		inquestiontype = entrycomplicate(moka.type,compObs,names=compNames)

		# def _dbgTest():
		# 	assert dualexpected.rows[h].type.verdepth == provob.verdepth+len(cusecrets)

		heig = dualexpected.rows[h].type.dpush(moat)

		against = entrycomplicate(heig,cusecrets,names=cunames)

		amt = upgrades.get(fou,0)

		if amt!=0: inquestion = downparent(against,inquestiontype,amt,inquestion)
                    
		if extract!=None: st = len(extract)

		if not against.compare(inquestiontype,odsc,thot,extract):
			print("within:")
			print("\t",against)
			print("\t",against.secrets[0].observe())
			print("\t",against.prepr(FormatterObject(None,fullrepresent=True),[]))
			print()
			print("\t",inquestiontype)
			print("\t",inquestiontype.secrets[0].observe())
			print("\t",inquestiontype.prepr(FormatterObject(None,fullrepresent=True),[]))
			print()
			print("\t",dualexpected)
			print("\t\t",dualexpected.prepr(FormatterObject(None,fullrepresent=True),[]))
			print("end")
			raise MalformedInheritancePath((heig,moka.type,[dualexpected.rows[a].name for a in range(h)],[a.name for a in guflat.flat[:fou]]))

		if extract!=None:
			for kt in range(st,len(extract)): extract[kt] = (extract[kt][0],extract[kt][1],extract[kt][2],owner)

		finob.append(SubRow(None,inquestion))
		moat = moat + ScopeDelta([(longflattenunravel(dualexpected.rows[h].name,dualexpected.rows[h].type.get_divisibility_si(),inquestion,provob.verdepth+len(cusecrets))[0],)])#,(-vv,provob.verdepth)
		# cusecrets = cusecrets +


		cusecrets = cusecrets + TypeRow(dualexpected.rows[h].name,dualexpected.rows[h].type,inquestion.simpush(SimpleDelta(len(cusecrets),inquestion.verdepth))).ripsingle()
		cunames = cunames + longlist(dualexpected.rows[h].name)

	return SubsObject(finob,verdepth=provob.verdepth)


def implicitcast(indesc,expected,provided,obj,blame=None,soften=False,extract=None,thot=None,odsc=None,owner=None):
	def _dbgEnter():
		obj.looseconforms(provided.get_divisibility_si())
	def _dbgExit(outp):
		outp.looseconforms(expected.get_divisibility_si())

	# bounce = 0

	ihfb = None

	if extract!=None: st = len(extract)
	eA = 0
	headE = expected
	while True:
		pA = 0
		headP = provided
		while True:
			# if bounce==1:
			# 	huahua = obj
			# 	obj = RefTree(name=expected.verdepth,core=DelayedSub(obj,obj.isSubOb(),ScopeDelta([(1,expected.verdepth)])),verdepth=expected.verdepth+1)
			# 	expected = expected.dpush(ScopeDelta([(1,expected.verdepth)]))
			# 	provided = provided.dpush(ScopeDelta([(1,provided.verdepth)]))
			# 	headE = headE.dpush(ScopeDelta([(1,headE.verdepth)]))
			# 	headP = headP.dpush(ScopeDelta([(1,headP.verdepth)]))
			# bounce += 1

			if headE.compare(headP,odsc,thot,extract):
				# if bounce>0:
				# 	print("MATCHED BETWEEN: ",headE,headP)
				if extract!=None:
					for kt in range(st,len(extract)): extract[kt] = (extract[kt][0],extract[kt][1],extract[kt][2],owner)
				provob = reparent(provided,pA,obj)
				try:
					au = downparent(expected,headE,eA,provob,extract=extract,thot=thot,odsc=odsc,owner=owner)
					# if bounce==1: 
					return au
					# return complicate(au,[DelayedComplication(huahua)])
				except MalformedInheritancePath as u:
					if ihfb==None: ihfb = u.ihfb
			if extract!=None:
				while st<len(extract): del extract[st]

			# bounce+=1

			headP,hpC,hpN = headP.diveIntoDualSubs()
			if headP==None: raise TypeMismatch(blame,expected,provided,indesc).ihfb(ihfb).soften(soften)
			if headP.origin==None: break
			headP = entrycomplicate(headP.origin[0],hpC,names=hpN)
			pA += 1

		headE,heC,heN = headE.diveIntoDualSubs()
		if headE==None or headE.origin==None:
			# print()
			# print("\t",ihfb)
			# print("\t",ihfb[0].verdepth)
			# print("\t",ihfb[1].verdepth)
			# print("\t",ihfb[0].prepr(FormatterObject(None,fullrepresent=True),[]))
			# print("\t",ihfb[1].prepr(FormatterObject(None,fullrepresent=True),[]))
			# print()
			# print(expected.verdepth)
			# print(provided.verdepth)
			# print("\t",expected.unwrap())
			# print("\t",provided.unwrap())
			# print()

			raise TypeMismatch(blame,expected,provided,indesc).ihfb(ihfb).soften(soften)
		headE = entrycomplicate(headE.origin[0],heC,names=heN)
		eA += 1
	





# found common ancestor?(first common ancestor) (second common ancestor does not have interesting properties.)
# 	add property to TypeMismatch that just prints underneath...
# 	expected inherits from ---> (one side)
# 	provided inherits from ---> (other side)

# 	print failed comparison...




class ContextYam:
	def __init__(self,operators=None,mergememo=None):
		self.operators = operators
		self.mergememo = {} if mergememo == None else mergememo
		# self.lastComputation = lastComputation
		# self.nextComputation = Computation()


	def mergedeltas(self,typerows):
		global hits
		global references

		suh = copy.copy(self.mergememo)
		for t in typerows: t.mergewith(suh)
		ya = ContextYam(self.operators,suh)

		# if references!=0: print("Current hit rate: ",100*float(hits)/float(references),"%")

		return ya



# spawn with your own...
# preserve memo over add...
# modify new elements that were added in...


class ScopeObject:
	def __init__(self,flat=None,prpush=None,popush=None,oprows=None):
		self.oprows     = oprows
		self.prepushes  = ScopeDelta() if prpush == None else prpush
		self.postpushes = ScopeDelta() if popush == None else popush
		self.flat = [] if flat == None else flat
		self.memo = []

		def _dbgTest():
			assert type(self.postpushes) is ScopeDelta
			assert type(self.prepushes) is ScopeDelta
			self.prepushes.conforms(len(self.flat)-self.prepushes.lenchange)
			self.postpushes.conforms(len(self.flat))

		for k in self.postpushes.pushes:
			assert len(k)==2
			assert k[0]<=0

	def addflat(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes,None if self.oprows == None else self.oprows.mergedeltas(newflat.flat))
	def invisadd(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
			assert len(ahjs)==len(self)
			assert self.beginlen()+len(newflat.flat)==ahjs.beginlen()
		if len(newflat.flat) == 0: return self
		if self.oprows != None: self.oprows.mergedeltas(newflat.flat)
		return ScopeObject(self.flat+newflat.flat,self.prepushes,self.postpushes+ScopeDelta([(-len(newflat.flat),len(self))]),self.oprows)
	def sneakadd(self,newflat):
		def _dbgEnter():
			self.setSafety(0)
			newflat.setSafety(len(self))
		def _dbgExit(ahjs):
			ahjs.setSafety(0)
		if len(newflat.flat) == 0: return self
		return ScopeObject(self.flat+newflat.flat,self.prepushes+ScopeDelta([(len(newflat.flat),len(self.flat))]),self.postpushes,None if self.oprows == None else self.oprows.mergedeltas(newflat.flat))


	# def posterase(self,amt):
	# 	if amt == 0: return self
	# 	return ScopeObject(self.flat,self.prepushes,self.postpushes+ScopeDelta([(amt-len(self),amt)]),self.oprows)
	def preerase(self,amt):
		if amt == 0: return self
		return ScopeObject(self.flat,self.prepushes+ScopeDelta([(amt,len(self.flat)-amt)]),self.postpushes,None if self.oprows == None else self.oprows)


	def setSafety(self,safe):
		# return
		# yooj = {}
		for i in range(len(self.flat)):
			# try:
			# 	self.flat[i].type.observe().hascorrectlinks(yooj)
			# 	if self.flat[i].obj!=None:self.flat[i].obj.observe().hascorrectlinks(yooj)
			# except Exception as u:
			# 	print("here's the tea")
			# 	print("\t",[a.name for a in self.flat[:i]])
			# 	print("\t",yooj)
			# 	print("\t",self.flat[i].name)
			# 	print("\t",self.flat[i].type.observe().prepr(FormatterObject(ScopeObject(self.flat[:i])),[]),self.flat[i].type.observe())
			# 	print("\t",self.flat[i].type.observe().prepr(FormatterObject(ScopeObject(self.flat[:i]),fullrepresent=True),[]),self.flat[i].type.observe().prepr(FormatterObject(None,fullrepresent=True),[]))
			# 	print("\t",self.flat[i].obj.observe().prepr(FormatterObject(ScopeObject(self.flat[:i])),[]),self.flat[i].obj.observe())
			# 	print("\t",self.flat[i].obj.observe().prepr(FormatterObject(ScopeObject(self.flat[:i]),fullrepresent=True),[]),self.flat[i].obj.observe().prepr(FormatterObject(None,fullrepresent=True),[]))
			# 	raise u
			# yooj[safe+i] = None if self.flat[i].obj==None else self.flat[i].obj.isSubOb()

			cr = self.postpushes.translateGentle(i)
			self.flat[i].setVerified()
			try:
				self.flat[i].setSafetyrow(safe+cr)
			except Exception as u:
				print()
				print(self)
				print(i,cr,self.flat[i].getSafetyrow())
				print()
				raise u

	def trimabsolute(self,amt):
		def _dbgEnter():
			self.setSafety(0)
		def _dbgExit(ahjs):
			assert len(self)-amt == len(ahjs)
			assert self.beginlen() == ahjs.beginlen()
		ahjs = ScopeObject(self.flat[:len(self.flat)-amt],-(-self.prepushes).subset(len(self.flat)-amt),self.postpushes,None if self.oprows == None else self.oprows)
		return ahjs


	def prepushPR(self,pushes):
		if pushes.isempty(): return self
		return ScopeObject(self.flat,pushes+self.prepushes,self.postpushes,None if self.oprows == None else self.oprows)


	def beginlen(self):
		return len(self.flat) - self.prepushes.lenchange
	def __len__(self):
		return len(self.flat) + self.postpushes.lenchange


	def flatnamespace(self):
		databus = [k.name for k in self.flat]
		for amt,lim in self.postpushes.pushes:
			databus = databus[:lim]+databus[lim-amt:]
		return databus
	def subprots(self):
		hama = []
		for k in range(len(self.flat)):
			if self.flat[k].obj!=None and self.postpushes.canTranslate(k):
				hama.append(self.postpushes.translate(k))
		for a in range(len(hama)):
			for b in range(a):
				assert hama[a]!=hama[b]
		return hama



	def acceptedlist(self):
		databus = []
		inrow=0
		outrow=0
		while inrow<len(self.flat):
			if self.prepushes.canTranslate(len(databus)):
				if (-self.prepushes).canTranslate(inrow):
					databus.append(self.flat[inrow].name)
				inrow+=1
			else:
				databus.append(None)
		while len(databus)<self.beginlen():databus.append(None)
		return databus


	def symextract(self,name,subs,carry=None,reqtype=False,limiter=None,pos=None,cosafety=None,errorcontext=None):
		def _dbgEnter():
			assert carry==None or isinstance(carry,Tobj)
			self.setSafety(0)
			for j in subs:
				assert type(j) is tuple and len(j) == 2
				assert type(j[1]) is tuple and len(j[1]) == 2
				if j[1][1]==False:
					j[1][0].setSafety(self.beginlen())
				else:
					j[1][0].setSafety(len(self))
		errorcontext = [] if errorcontext == None else errorcontext
		def compachelper(row):
			def _dbgExit(ahjs):
				if ahjs != None:
					outp,ty = ahjs
					assert isinstance(outp,Tobj)
					assert isinstance(ty,Tobj)
					# if reqtype:
					ty.setSafety(len(self))
					# if pos!=None: assert outp.row!=0 or outp.column!=0
					outp.setVerified()
					outp.setSafety(len(self))

			if row == 0:
				return (u_type(len(self)),u_type(len(self)))
			cr=self.postpushes.translateGentle(row)
			curr = self.flat[row].type.observeAT(len(self))
			# curr = self.flat[row].type.dpush(ScopeDelta([(len(self)-cr,min(cr,len(self)))]))
			# bedoin,cuarg,ntype = curr.extractfibrationSubs(self,subs,minsafety=cosafety,maxsafety=None if self.flat[row].silent==None else self.flat[row].silent['contractible'],blame=pos)
			drargs,ntype = curr.extractfibrationSubs(self,subs,minsafety=cosafety,maxsafety=None if self.flat[row].silent==None else self.flat[row].silent['contractible'],blame=pos)

			# print(len(cuarg.rip()),longcount(cuarg),len(longlist(cuarg)))
			# assert len(cuarg.rip()) == longcount(cuarg) == len(longlist(cuarg))

			# ntype = complicate(ntype,cuarg.rip(),names=longlist(cuarg))
			# drargs = SubsObject(cuarg.extractbetween(bedoin),verdepth=len(self)) if len(bedoin) else None

			if not self.postpushes.canTranslate(row) or limiter!=None:
				# obj = self.flat[row].obj.dpush(ScopeDelta([(len(self)-cr,min(cr,len(self)))]),exob=drargs)
				obj = self.flat[row].obj.observeAT(len(self),exob=drargs)
				transferlines(obj,pos)
			elif self.flat[row].obj == None:
				obj = RefTree(cr,drargs,verdepth=len(self),pos=pos)
			else:
				obj = RefTree(
					cr,
					drargs,
					verdepth=len(self),
					pos=pos,
					core=self.flat[row].obj.observe()
					# core=DelayedSub(self.flat[row].obj,self.flat[row].obj.isSubOb(),ScopeDelta([(len(self)-cr,min(cr,len(self)))]))
				)
			return obj,ntype

		if len(self.flat) == 0:
			return (u_type(verdepth=len(self)),u_type(verdepth=len(self))) if reqtype else u_type(verdepth=len(self))

		possib = []
		for row in reversed(range(len(self.flat))):
			if limiter!= None and row<limiter: break
			if self.flat[row].name != name: continue
			if limiter== None and not (-self.prepushes).canTranslate(row): continue

			errorcontext.insert(0,(name,self.flat[row].type,self,None))
			possib.append(row)
		mmatch = len(errorcontext)
		for row in possib:
			try:
				outp,comptype = compachelper(row)
			except LanguageError as u:
				mmatch -= 1
				if u.soft and len(possib)!=1:
					errorcontext[mmatch] = (errorcontext[mmatch][0],errorcontext[mmatch][1],errorcontext[mmatch][2],u)
					continue

				u.callingcontext(errorcontext,mmatch)
				raise u

			if outp!=None and carry!=None: outp = implicitcast(self,carry,comptype,outp,blame=pos)
			if reqtype: return (outp,comptype)
			return outp


	def precidence(self,ind):
		for j in range(len(self.oprows.operators)):
			if ind in self.oprows.operators[j][0]:
				return (j,self.oprows.operators[j][1]['associate'])
	def __repr__(self):
		output = []
		for d in self.flat:
			output.append((d.name if type(d.name) is str else repr(d.name))+("|" if d.obj!=None else ""))
		return repr(output)+repr(self.postpushes)+" -- "+repr(self.prepushes)








def shortwidereferencerecurse(obj,si):
	if type(si) is not list: return [obj]
	cu = []
	for s in range(len(si)): cu = cu+shortwidereferencerecurse(obj.reference(s),si[s])
	return cu

def amorphwidereference(obj,ty,si):
	if type(si) is not list: return [obj]
	if conservativeeq(ty.get_sem_si(si),si):
		if obj==None: return [None]*longcount(si)
		return shortwidereferencerecurse(obj,si)
	return [None if j.obj==None else j.obj.observe() for j in ty.flatten(ScopeDelta(),si,obj=None if obj==None else DelayedComplication(obj)).flat]




def widereference(obj,ty,si):
	# def _dbgTest():
	# 	assert obj.verdepth==ty.verdepth
	if type(si) is not list: return [obj]
	if conservativeeq(ty.ob.get_sem_si(si,ty.srows),si):
		tyvd = ty.ob.verdepth+ty.srows.lenchange
		hey = shortwidereferencerecurse(obj,si)
		return [hey[0]]+[hey[s].dpush(ScopeDelta([(s,tyvd)])) for s in range(1,len(hey))]
	return [a.obj for a in ty.ob.flatten(ty.srows,si,obj=obj).flat]
	# <><><> use unwrflatten here...

	# unwrflatten
	# return [complicate(jast[k],[DelayedComplication(jast[l]) for l in range(k)]) for k in range(len(jast))]






def juris(name):
	if type(name) is list: return [juris(x) for x in name]
	return (name,None)


references = 0
hits = 0


class DelayedTypeRow:
	def __init__(self,name,ty,obj=None,silent=None):
		self.name = name
		self.type = ty
		self.obj  = obj
		self.silent = silent
		def _dbgTest():
			self.type.assertValid()
			if self.obj!=None: self.obj.assertValid()
	def canbetranslated(self,pushes):
		self.type.canbetranslated(pushes)
		if self.obj!=None: self.obj.canbetranslated(pushes)
	def observe(self):
		return TypeRow(self.name,self.type.observe(),None if self.obj==None else self.obj.observe(),self.silent)
	def setVerified(self):
		if self.type != None: self.type.setVerified()
		if self.obj != None: self.obj.setVerified()
	def setSafetyrow(self,safe):
		if self.type != None: self.type.setSafety(safe)
		if self.obj != None: self.obj.setSafety(safe)
	def getSafetyrow(self):
		res = None
		if self.type != None:
			res = self.type.getSafety()
			if self.obj!=None and res!=None:self.obj.setSafety(res)
		if res==None and self.obj!=None:
			res = self.obj.getSafety()
			if self.type!=None and res!=None:self.type.setSafety(res)
		return res
	def dpush(self,rows):
		"""dbg_ignore"""
		return DelayedTypeRow(self.name,self.type.dpush(rows),None if self.obj==None else self.obj.dpush(rows),self.silent)

	def detect(self,ranges):
		if self.type.ob.detect(self.type.srows+ranges): return True
		if self.obj!=None:
			if self.obj.ob.detect(self.obj.srows+ranges): return True
		return False

	def look(self,result,lowerbound=False):
		if self.type.srows.isempty(): self.type.ob.look(result,lowerbound=lowerbound)
		else:
			self.type.srows.lookmemo=set()
			self.type.ob.advlook(result,self.type.srows,lowerbound=lowerbound)
		if self.obj!=None:
			if self.obj.srows.isempty(): self.obj.ob.look(result,lowerbound=lowerbound)
			else:
				self.obj.srows.lookmemo=set()
				self.obj.ob.advlook(result,self.obj.srows,lowerbound=lowerbound)


	def mergewith(self,suh):
		global hits
		global references
		if not self.type.srows.isempty():
			k = self.type.srows
			j = suh.get(k)
			references+=1
			if j!=None:
				hits+=1
				self.type.srows = j
			else: suh[k] = k
		if self.obj!=None and not self.obj.srows.isempty():
			k = self.obj.srows
			j = suh.get(k)
			references+=1
			if j!=None:
				hits+=1
				self.obj.srows = j
			else: suh[k] = k


class SimpleDelta:
	def __init__(self,amt,lim):
		self.amt = amt
		self.lim = lim
		# self.mem1 = {}
		self.mem2 = {}
		def _dbgTest():
			assert amt!=0

# def _dbgEnter_simpush(self,alo,outp):
# 	s
def _dbgExit_simpush(self,alo,outp):
	if type(self) is not TypeRow:
		ma = self.isSubOb()
		if type(ma) is int:
			if ma>=alo.lim: ma += alo.amt
		# print(outp.isSubOb(),ma)
			if outp.isSubOb() != ma:
				print("\t",outp.isSubOb(),ma,self.verdepth,outp.verdepth)
			assert outp.isSubOb() == ma

# 
# simpush may need to change the core...




class TypeRow:

	def __hash__(self):
		def wwah(si):
			if type(si) is not list: return hash(si)
			return hash(tuple(wwah(s) for s in si))
		return hash((wwah(self.name),self.type,self.obj))


	def setVerified(self):
		if self.type != None: self.type.setVerified()
		if self.obj != None: self.obj.setVerified()
	def setSafetyrow(self,safe):
		if self.type != None: self.type.setSafety(safe)
		if self.obj != None: self.obj.setSafety(safe)
	def getSafetyrow(self):
		res = None
		if self.type != None:
			res = self.type.getSafety()
			if self.obj!=None and res!=None:self.obj.setSafety(res)
		if res==None and self.obj!=None:
			res = self.obj.getSafety()
			if self.type!=None and res!=None:self.type.setSafety(res)
		return res
	def __init__(self,name,ty,obj=None,silent=None):
		self.name = name
		self.type = ty
		self.obj  = obj
		self.silent = silent
		if type(ty) is Lambda or type(ty) is SubsObject: assert False
		# assert self.type != None or self.obj != None
		assert type(self.type) is not Strategy or self.type.type != None or self.obj != None
		def _dbgTest():
			assert self.type==None or isinstance(self.type,Tobj)
			assert self.obj == None or isinstance(self.obj,Tobj)
	def delay(self):
		return DelayedTypeRow(self.name,DelayedComplication(self.type),None if self.obj==None else DelayedComplication(self.obj),self.silent)

	# def TypeRow(self,depth):
	# 	code = self.readChar()
	# 	name = self.readStrInc() if code in 'acegi' else None
	# 	ty   = self.generic(depth)
	# 	obj  = self.generic(depth) if code in 'ab' else None
	# 	silent   = code in 'ghij'
	# 	contract = self.readNum() if code in 'efij' else None
	# 	return TypeRow(name,ty,obj,{'silent':silent,'contractible':contract})


	def writefile(self,file):
		file.writeChar(["a","b","c","d","e","f","g","h","i","j"][(0 if self.obj!=None else 1 if self.silent==None else 1+int(self.silent['silent'])*2+int(self.silent['contractible']!=None))*2+int(self.name==None)])
		if self.name!=None: file.writeStrInc(self.name)
		self.type.writefile(file)
		if self.obj!=None: self.obj.writefile(file)
		elif self.silent!=None and self.silent['contractible']!=None: file.writeNum(self.silent['contractible'])

	# def ddpush(self,amt,lim,repls=None,replsrc=None):
	# 	return TypeRow(self.name,self.type.ddpush(amt,lim,repls,replsrc),None if self.obj == None else self.obj.ddpush(amt,lim,repls,replsrc),self.silent)
	def detect(self,ranges):
		return self.type.detect(ranges) or self.obj!=None and self.obj.detect(ranges)


	def ripsingle(self):
		if type(self.name) is list:
			return widereference(DelayedComplication(self.obj),DelayedComplication(self.type),self.name)
			# return [DelayedComplication(ho[0])]+[DelayedComplication(ho[d],ScopeDelta([(d,self.obj.verdepth)]) ) for d in range(1,len(ho))]
		else:
			return [DelayedComplication(self.obj)]


	def look(self,result,lowerbound=False):
		self.type.look(result,lowerbound=lowerbound)
		if self.obj!=None: self.obj.look(result,lowerbound=lowerbound)
	def advlook(self,result,pushes,lowerbound=False):
		self.type.advlook(result,pushes,lowerbound=lowerbound)
		if self.obj!=None: self.obj.advlook(result,pushes,lowerbound=lowerbound)

	# def changeVD(self,amt):
	# 	return TypeRow(self.name,self.type.changeVD(amt),None if self.obj==None else self.obj.changeVD(amt),self.silent)
	def simpush(self,alo):
		return TypeRow(self.name,self.type.simpush(alo),None if self.obj == None else self.obj.simpush(alo),self.silent)
	def dpush(self,pushes):
		"""dbg_ignore"""
		return TypeRow(self.name,self.type.dpush(pushes),None if self.obj == None else self.obj.dpush(pushes),self.silent)



	def vershortcut(self,indesc):
		return TypeRow(self.name,self.type.verify(indesc),None if self.obj == None else self.obj.verify(indesc),self.silent)
	

	def prepr(self,context,trail,word=None):
		if word==None: word = juris(self.name)
		res = "" if self.name == None else pmultilinelist(self.name,context,word)+":"
		if self.silent!=None and self.silent['silent']:
			if res=="": res = "?:"
			else: res = res[:-1]+"?:"
		if self.type != None: res = res+self.type.prepr(context,trail)
		if self.obj != None: res = res+" = "+self.obj.prepr(context,trail)
		return res
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None,word=None):
		if word==None: word = juris(self.name)
		def calls(context_,out,prepend):
			if self.obj != None:
				self.obj.pmultiline(context,trail,out,indent,prepend,postpend,callback=callback)
			else:
				if callback == None:
					out.append("\t"*indent+prepend+postpend)
				else:
					callback(context,out,prepend+postpend)
		name = "" if self.name == None else pmultilinelist(self.name,context,word)+":"
		if self.silent!=None and self.silent['silent']:
			if name=="": name = "?:"
			else: name = name[:-1]+"?:"
		if self.type==None:
			calls(context,out,prepend+name+": INFERRING TYPE = "+postpend)
		else:
			self.type.pmultiline(context,trail,out,indent,prepend+name," = " if self.obj != None else "",calls)
	def __repr__(self):
		return self.prepr(FormatterObject(None),[])
class SubRow:
	def setVerified(self):
		self.obj.setVerified();
	def setSafetyrow(self,safe):
		self.obj.setSafety(safe)
	def getSafetyrow(self):
		return self.obj.getSafety()

	def __init__(self,name,obj):
		self.name = name
		self.obj  = obj
		def _dbgTest():
			assert isinstance(self.obj,Tobj)
	# def ddpush(self,amt,lim,repls=None,replsrc=None):
	# 	return SubRow(self.name,self.obj.ddpush(amt,lim,repls,replsrc))
	def detect(self,ranges):
		return self.obj.detect(ranges)
	def dpush(self,pushes):
		"""dbg_ignore"""
		return SubRow(self.name,self.obj.dpush(pushes))


	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		return self.obj.compare(other.obj,odsc,thot,extract,lefpush,rigpush)
	def prepr(self,context,trail):
		res = "" if self.name == None or context!=None else pmultilinelist(self.name,context,juris(self.name))+" = "
		res = res+self.obj.prepr(context,trail)
		return res
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		name = "" if self.name == None else pmultilinelist(self.name,context,juris(self.name))+" = "
		self.obj.pmultiline(context,trail,out,indent,prepend+name,postpend,callback)
	def __repr__(self):

		return self.prepr(FormatterObject(None),[])


class Inspection:
	def __init__(self,root,inspect):
		self.root = root
		self.inspect = inspect
	def __eq__(self,other):
		return type(other)==Inspection and (self.root,self.inspect)==(other.root,other.inspect)
	def __repr__(self):
		return repr(self.root)+repr(self.inspect)

def inspectref(mak,ins):
	while type(mak) is tuple and len(ins):
		mak = mak[ins[0]]
		ins = ins[1:]
	if type(mak) is Inspection:
		return Inspection(mak.root,mak.inspect+ins)
	if type(mak) is list:
		return mak+ins
	if len(ins):
		return Inspection(mak,ins)
	return mak




# fullunwrapmemo


# flatnermemo


# not all memos should qualify. modify the existing memo so that if you detect anything above the name, you do not memoize.

# more specifically, if you detect anythingufck (x has a core of () )







			# aftburn = self.verdepth+pushes.lenchange
			# jsi = self.si[:len(exob.subs)] if len(self.si)>len(exob.subs) else self.si
			# nexob = SubsObject(exob.subs[:len(self.si)],verdepth=exob.verdepth) if len(exob.subs)>len(self.si) else exob
			# adob = None
			# if len(exob.subs)>len(self.si):
			# 	adob = SubsObject(exob.subs[len(self.si):],verdepth=exob.verdepth)#.dpush(ScopeDelta([(aftburn-exob.verdepth,exob.verdepth)]),frozen=True)
			# res = self.obj.dpush(pushes+ScopeDelta([(coflattenunravel(jsi,nexob,aftburn),),(-longcount(jsi),aftburn)]),exob=adob,frozen=frozen,selective=selective)
			# if len(self.si)>len(exob.subs): res = res.addlambdasphase2(self.si[len(exob.subs):],pos=self)
			# if selective==None: pushes.setmemo(self,exob,frozen,res)
			# return res




class Tobj:
	def innertrim(self,si=None,disgrace=None):#Tobj
		raise InvalidSplit()

	# def paredown(self):
	# 	return self

	def unwrflatten(self,obj=None):
		mycore = self
		mysds = ScopeDelta()
		myargs = None
		while type(mycore) is ScopeComplicator or type(mycore) is RefTree and mycore.core!=None or type(mycore) is Lambda:
			if type(mycore) is ScopeComplicator:
				mysds = mycore.correction()+mysds
				mycore = mycore.core
			elif type(mycore) is Lambda:
				if myargs.subs==None or len(mycore.si)>len(myargs.subs): return None
				nexob = myargs if len(mycore.si)==len(myargs.subs) else SubsObject(myargs.subs[:len(mycore.si)],verdepth=myargs.verdepth)
				myargs = None  if len(mycore.si)==len(myargs.subs) else SubsObject(myargs.subs[len(mycore.si):],verdepth=myargs.verdepth)
				mysds  = mysds + ScopeDelta([(coflattenunravel(mycore.si,nexob,mycore.verdepth+mysds.lenchange),),(-longcount(mycore.si),mycore.verdepth+mysds.lenchange)])
				mycore = mycore.obj
			else:
				if mycore.args!=None: myargs = mycore.args.dpush(mysds) if myargs==None else SubsObject(mycore.args.dpush(mysds).subs+myargs.subs,verdepth=mycore.args)
				mysds = mycore.unwrc()+mysds
				mycore = mycore.core

		# if myargs!=None or True:
		# 	mycore = mycore.dpush(mysds,exob=myargs)
		# 	mysds = ScopeDelta()
		si = mycore.get_si(mysds)
		# print("GUAGUA: ",si)
		if si==None: return None
		return mycore.flatten(mysds,si,obj=obj)

# .core.core



	def looseconforms(self,ba):
		if type(self) is SubsObject and type(ba) is list:
			s = 0
			assert len(ba)==len([s for s in ba if ba != False])
			for k in ba:
				if k!=False:
					self.subs[s].obj.looseconforms(k)
					s+=1

	def isfrozen(self):
		return False
	def decode(self):
		return self
	def getbecsafety(self):
		return None
	def isemptytype(self):
		return False



	def get_sem_si(self,sem,pushes=None):
		if type(self) is Lambda: return self.obj.get_sem_si(sem,pushes)
		if type(self) is ScopeComplicator: return self.core.get_sem_si(sem,self.correction() if pushes==None else self.correction()+pushes)
		if type(self) is Strategy: return self.type.get_sem_si(sem,pushes)
		if type(self) is DualSubs: return self.semavail(sem)
		if type(self) is RefTree and self.core!=None:
			return self.core.get_sem_si(sem,self.unwrc() if pushes==None else self.unwrc()+pushes)
		if type(self) is RefTree and self.src==None and pushes!=None:
			mow = pushes.translate(self.name,inlen=self.verdepth)
			if type(mow) is tuple: return mow[0].get_sem_si(sem,mow[1])
		return None

	def get_si(self,pushes=None):
		if type(self) is Lambda: return self.obj.get_si(pushes)
		if type(self) is ScopeComplicator: return self.core.get_si(self.correction() if pushes==None else self.correction()+pushes)
		if type(self) is Strategy: return self.type.get_si(pushes)
		if type(self) is DualSubs: return [row.name for row in self.rows]
		if type(self) is RefTree and self.core!=None:
			return self.core.get_si(self.unwrc() if pushes==None else self.unwrc()+pushes)
		if type(self) is RefTree and self.src==None and pushes!=None:
			mow = pushes.translate(self.name,inlen=self.verdepth)
			if type(mow) is tuple: return mow[0].get_si(mow[1])
		print("get failed",self)
		return None

	def get_divisibility_si(self,pushes=None):
		if type(self) is Lambda: return self.obj.get_divisibility_si(pushes)
		if type(self) is ScopeComplicator: return self.core.get_divisibility_si(self.correction() if pushes==None else self.correction()+pushes)
		if type(self) is Strategy: return self.type.get_divisibility_si(pushes)
		if type(self) is DualSubs: return [row.type.get_divisibility_si(pushes) if row.obj==None else False for row in self.rows]
		if type(self) is RefTree and self.core!=None:
			return self.core.get_divisibility_si(self.unwrc() if pushes==None else self.unwrc()+pushes)
		if type(self) is RefTree and self.src==None and pushes!=None:
			mow = pushes.translate(self.name,inlen=self.verdepth)
			if type(mow) is tuple: return mow[0].get_divisibility_si(mow[1])
		return True

	def get_corrector_si(self,pushes=None):
		if type(self) is Lambda: return self.obj.get_corrector_si(pushes)
		if type(self) is ScopeComplicator: return self.core.get_corrector_si(self.correction() if pushes==None else self.correction()+pushes)
		if type(self) is Strategy: return self.type.get_corrector_si(pushes)
		if type(self) is DualSubs: return ([row.type.get_corrector_si(pushes) if row.obj==None else False for row in self.rows],self.get_si(pushes))
		if type(self) is RefTree and self.core!=None:
			return self.core.get_corrector_si(self.unwrc() if pushes==None else self.unwrc()+pushes)
		if type(self) is RefTree and self.src==None and pushes!=None:
			mow = pushes.translate(self.name,inlen=self.verdepth)
			if type(mow) is tuple: return mow[0].get_corrector_si(mow[1])
		return (None,None)




	def setVerified(self):
		assert self.verdepth!=None
		pass
	def setSafety(self,safe):
		if safe == None: return
		if hasattr(self,'foclnsafety'):
			if self.foclnsafety != safe: assert False
		else:
			self.foclnsafety = safe
			downdeepverify(self,safe)
	def getSafety(self):
		if hasattr(self,'foclnsafety'): return self.foclnsafety
		else:
			safe = updeepverify(self)
			if safe != None: self.foclnsafety = safe
			return safe

	def flatten(self,delta,mog,assistmog=None,prep=None,obj=None,fillout=None,then=False):
		if type(mog) is list:

			if type(self) is RefTree:
				if self.core==None:
					if delta.isempty():
						yap = self.mangle_UE()
						if yap!=None: return yap.flatten(delta,mog,assistmog,prep,obj,fillout,then)
					else:
						return self.dpush(delta).flatten(ScopeDelta(),mog,assistmog,prep,obj,fillout,then)
				else:
					if self.args == None:
						return self.core.flatten(self.unwrc()+delta,mog,assistmog,prep,obj,fillout,then)
					else:
						yap = self.unwrap()
						if yap!=None: return yap.flatten(delta,mog,assistmog,prep,obj,fillout,then)


			if type(self) is ScopeComplicator:
				return self.core.flatten(self.correction()+delta,mog,assistmog,prep,obj,fillout,then)
			# if type(self) is RefTree:
			# 	yap = self.mangle_UE()
			# 	if yap!=None: return yap.flatten(delta,mog,assistmog,prep,obj,fillout,then)
			print("-=-=-=-=-=-")
			print(self)
			raise InvalidSplit()

		yatta = self.verdepth+delta.lenchange

		targo = yatta-(longcount(prep) if prep!=None else 0)

		if prep != None: njprep = prep if targo==prep.verdepth else prep.simpush(SimpleDelta(targo-prep.verdepth,prep.verdepth))
		pushob = None
		if obj!=None:
			yar = obj.ob.verdepth+obj.srows.lenchange
			pushob = obj if yatta==yar else obj.dpush(ScopeDelta([(yatta-yar,yar)]))
		if prep == None or len(njprep.rows)==0:
			outp = ScopeObject([DelayedTypeRow(mog,DelayedComplication(self,delta),pushob)])
		else:
			coron = self if delta.isempty() else self.dpush(delta)
			outp = ScopeObject([DelayedTypeRow(mog,DelayedComplication(coron.addfibration(njprep)),None if pushob == None else DelayedComplication(pushob.observe().addlambdas(njprep)))])
		if then: return (outp,delta)
		return outp
	def isemptyinst(self,si,prep=None):
		return False
	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not int: raise InvalidSplit()
		prep = prep if prep == None or limit==prep.verdepth else prep.simpush(SimpleDelta(limit-prep.verdepth,prep.verdepth))

		return RefTree(name=mog,args=prep,verdepth=limit)
	def addfibration(self,args,pos=None):
		if len(args) == 0:
			return entrycomplicate(self,args.rip(),pos=self,names=longlist(args))
			# return self.dpush( ScopeDelta([(-shaz,self.verdepth-shaz)]))
		return Strategy(args,self,verdepth=self.verdepth-longcount(args),pos=self if pos==None else pos)
	def addlambdas(self,args,pos=None):
		starter = self.verdepth-longcount(args)
		si = args.semavail()
		disgrace = ([],[])
		largs = args.trimallnonessential(si,disgrace=disgrace)

		# ntype = self
		ntype = compassionate_reshift(self,disgrace[0],disgrace[1])
		def _dbgTest():
			assert len(disgrace[1]) == longcount(args)-longcount(si)
			ntype.setSafety(self.verdepth-longcount(args)+longcount(si))
		# if len(disgrace[0]): ntype = complicate(ntype.dpush(ScopeDelta([(c[1],c[0],ntype.verdepth,0) for c in disgrace[0]])),disgrace[1],names=disgrace[2])
		return ntype.addlambdasphase2(si,pos=pos)
	def addlambdasphase2(self,si,pos=None):
		def _dbgExit(outp):
			outp.setSafety(self.verdepth - longcount(si))
			assert outp.verdepth == self.verdepth - longcount(si)
		if len(si)==0: return self
		if type(self) is Lambda:
			return Lambda(si+self.si,self.obj,verdepth=self.verdepth-longcount(si),pos=self if pos==None else pos)
		elim=0
		fafter = self.verdepth
		ndepth = self.verdepth
		goffset = 0
		starter = fafter-longcount(si)
		outp = self
		if type(self) is ScopeComplicator:
			goffset = len(self.secrets)
			outp = self.core
		if type(outp) is RefTree and outp.name<starter and outp.args!=None:
			elim=0
			while elim<len(si) and elim<len(outp.args.subs):
				ndepth = starter+longcount(si[:len(si)-elim-1])
				if outp.args.subs[len(outp.args.subs)-1-elim]==None: break
				if not outp.args.subs[len(outp.args.subs)-1-elim].obj.isemptyinst(striphuman(ndepth,si[len(si)-1-elim])[0]): break
				thisdepth = longcount(si[len(si)-elim-1])
				valid = True
				if outp.src!=None:
					if outp.src.detect(ScopeDelta([(-thisdepth,ndepth)])): 
						valid = False
				for k in outp.args.subs[:len(outp.args.subs)-1-elim]:
					if k.obj.detect(ScopeDelta([(-thisdepth,ndepth)])):
						valid = False
						break
				if not valid: break
				elim+=1
			if elim:
				# def _dbgTest():
				# 	if ndepth==fafter:
				# 		print(si)
				# 		print(elim)
				# 		print(starter+longcount(si[:len(si)-elim]))
				# 		print(starter)
				# 		print(fafter)
				ndepth = starter+longcount(si[:len(si)-elim])
				stretch = ScopeDelta([(ndepth-fafter,ndepth)])
				nsubs = SubsObject([SubRow(None,k.obj.dpush(stretch)) for k in outp.args.subs[:len(outp.args.subs)-elim]],verdepth=ndepth) if len(outp.args.subs)!=elim else None
				# core = None
				# if outp.core != None:
				# 	core = outp.core.dpush_ds(ScopeDelta([(ndepth-fafter,ndepth)]),outp.name)
				outp = RefTree(outp.name,nsubs,None if outp.src==None else outp.src.dpush(stretch),verdepth=ndepth+goffset,pos=outp,core=outp.core)
		if type(self) is ScopeComplicator:
			if elim==0:
				outp = self
			else:
				stretch = ScopeDelta([(ndepth-fafter,ndepth)])
				outp = complicate(outp,[secret.dpush(stretch) for secret in self.secrets],names=self.names)
		if len(si)==elim: return outp
		return correctLambda(si[:len(si)-elim],outp,ScopeDelta(),verdepth=starter,pos=self if pos==None else pos)


	def diveIntoDualSubs(self):
		secrets = []
		names = []
		while type(self) is not DualSubs:
			if type(self) is ScopeComplicator:
				secrets = secrets + self.secrets
				names = names + self.names
				self = self.core
			elif type(self) is RefTree:
				if self.core!=None:
					self = self.unwrapOne()
				else: self = self.mangle_UE()
			else: return (None,secrets,names)
		return (self,secrets,names)
	def asDualSubs(self):
		self = self.decode()
		if type(self) is RefTree: self = self.mangle_UE()
		if type(self) is not DualSubs: return None
		return self


	def extractfibration(self,indesc,si,blame=None):
		if len(si)==0: return (DualSubs(verdepth=self.verdepth),self)
		try:
			carry = self.trimallnonessential(si[:min(len(si),len(self.args.semavail()))]+([None]*max(0,len(self.args.semavail())-len(si)))) if type(self) is Strategy else self
		except InvalidSplit as u:
			raise u.reblame(blame,self.args,si,indesc)
		ac = []
		while len(si)>len(ac):
			carry = carry.decode()
			if type(carry) is RefTree:
				mogo = carry.mangle_FE()
				if mogo!=None: carry = mogo
			if type(carry) is not Strategy:
				raise NonLambdaTypeError(blame,self,indesc)
			ac = ac + carry.args.rows
			carry = carry.type
		advdepth = self.verdepth+longcount([a.name for a in ac[:len(si)]])
		if len(si)<len(ac):
			carry = carry.addfibration(DualSubs(ac[len(si):],verdepth=advdepth))
			ac = ac[:len(si)]
		return (DualSubs(ac,verdepth=self.verdepth),carry)

	def extractfibrationSubs(self,indesc,inflow,minsafety=None,maxsafety=None,blame=None,preargs=None,preceed=None):
		def _dbgEnter():
			assert len(indesc)==self.verdepth
			if preargs!=None: assert preargs.verdepth==len(indesc)-(0 if preceed==None else len(preceed[0]))



		# 	length of indesc is unconstrained...


		# inflow ---> indesc.beginlen() and len(indesc)
		# self   --->                       len(indesc)


		# self.verdepth++
		#   len(indesc)++
		#   inflow.fin ++

		# increase len(indesc)...
		# by inserting some TypeRows.
		# do not mess with beginlen()...
		# so add prepush as well.
		if len(inflow)==0: return None,self
		if preceed == None: preceed = ([],[])
		carry = self
		earlyabort = True
		goneonce=False
		ac = []
		if type(carry) is ScopeComplicator:
			preceed = (preceed[0] + carry.secrets,preceed[1] + carry.names)
			pob = SimpleDelta(len(carry.secrets),self.verdepth)
			inflow = [(o[0],(o[1][0] if o[1][1]==False else o[1][0].simpush(pob),o[1][1] if type(o[1][1]) is bool else o[1][1].simpush(pob))) for o in inflow]
			return carry.core.extractfibrationSubs(indesc.sneakadd(ScopeObject([DelayedTypeRow(None,a) for a in carry.secrets])),inflow,minsafety,maxsafety,blame,preargs,preceed)
		while True:
			if type(carry) is ScopeComplicator: break
			if type(carry) is RefTree:
				mogo = carry.mangle_FE()
				if mogo!=None: carry = mogo
			if type(carry) is not Strategy: break
			goneonce=True
			oflow = []
			ac = ac + carry.args.rows
			midflow = DualSubs(ac,verdepth=self.verdepth).compacassign(inflow,oflow,minsafety)
			carry = carry.type
			if not len(oflow): break
		if not goneonce: raise VariableAssignmentError(blame,inflow[0][0])
		(cuarg,earlyabort),(indesc,ndelta) = DualSubs(ac,verdepth=self.verdepth).peelcompactify(indesc,midflow,then=True,earlyabort=earlyabort)
		if minsafety!=None: minsafety -= len(ac)
		gc = longcount([k.name for k in ac])
		pob = SimpleDelta(gc,len(indesc)-gc)
		inflow = [(o[0],(o[1][0] if o[1][1]==False else o[1][0].simpush(pob),o[1][1] if type(o[1][1]) is bool else o[1][1].simpush(pob))) for o in oflow]
		# cuarg = cuarg.rows
		carry = carry.dpush(ndelta)

		lensi = 0
		while lensi<len(cuarg.rows) and cuarg.rows[lensi].obj!=None:lensi+=1
		if lensi<len(ac):
			carry = carry.addfibration(DualSubs(cuarg.rows[lensi:],verdepth=cuarg.verdepth+longcount([a.name for a in cuarg.rows[:lensi]])))
			ac = ac[:lensi]
			cuarg = DualSubs(cuarg.rows[:lensi],verdepth=cuarg.verdepth)
		if any(k.obj==None for k in cuarg.rows): raise LanguageError(blame,"Hole in arguments list")

		bedoin = DualSubs(ac,verdepth=self.verdepth)
		if len(bedoin):
			preargs = SubsObject(([] if preargs==None else preargs.subs)+cuarg.extractbetween(bedoin,hiju=preceed),verdepth=self.verdepth-len(preceed[0]))
		preceed = (preceed[0] + cuarg.rip(),preceed[1] + longlist(cuarg))
		if len(inflow):
			return carry.extractfibrationSubs(indesc,inflow,minsafety,None if maxsafety==None else maxsafety-lensi,blame,preargs,preceed)
		if maxsafety!=None and lensi!=0 and lensi<maxsafety: raise LanguageError(blame,"Not enough parameters").soften(True)
		# try:
		return preargs,entrycomplicate(carry,preceed[0],names=preceed[1])
		# except:
		# 	print("-=-=-=-")
		# 	print("\t",[k.getSafety() for k in preceed[0]])
		# 	print("\t",carry.getSafety())
		# 	assert False


	def rip(self):
		cu = []
		for row in self.rows:
			cu = cu+row.ripsingle()
			# if type(row.name) is list:
			# 	ho = row.obj.widereference(row.name)
			# 	cu = cu+[ho[0]]+[ho[d].dpush(ScopeDelta([(d,self.verdepth+len(cu))])) for d in range(1,len(ho))]
			# else:
			# 	cu.append(row.obj)
		return cu


	def deepreference(self,su):
		k = self
		for s in su: k = k.reference(s)
		return k
	def reference(self,s,args=None):
		def _dbgEnter():
			if args!=None: args.setSafety(self.verdepth)
		if type(self) is SubsObject:
			if self.subs[s]==None: return None
			if args!=None:
				return self.subs[s].obj.dpush(ScopeDelta(),exob=args)
			return self.subs[s].obj
		elif type(self) is ScopeComplicator:
			return entrycomplicate(self.core.reference(s,args=None if args==None else args.simpush(SimpleDelta(len(self.secrets),self.verdepth))),self.secrets,names=self.names)
		elif type(self) is Lambda:
			mak = self.dpush(ScopeDelta(),exob=args,frozen=True).reference(s)
			if mak == None or mak.isfrozen(): raise DpushError
			return mak
		elif type(self) is RefTree and self.core!=None and type(self.isSubOb()) is tuple:
			return self.unwrapOne(selective=s).reference(s,args=args)
		if args!=None and args.isfrozen(): raise DpushError()
		return RefTree(src=self,name=s,args=args,verdepth=self.verdepth,pos=self)



	def __repr__(self):
		return self.prepr(FormatterObject(None),[])





# finish isSubOb and the translator for delaywedsubs

	def isSubOb(self):
		# def _dbgExit(outp):
		# 	assert type(outp) is not bool
		def _dbgEnter():
			assert self.verdepth!=None
		# def _dbgExit(outp):
		# 	assert outp
		if type(self) is ScopeComplicator:
			def sah(k):
				if type(k) is Inspection:
					if k.root<self.verdepth: return k
					else: return inspectref(self.secrets[k.root-self.verdepth].isSubOb(),k.inspect)
				if type(k) is int:
					if k<self.verdepth: return k
					else: return self.secrets[k-self.verdepth].isSubOb()
				if type(k) is tuple:
					return tuple(sah(h) for h in k)
				return k
			return sah(self.core.isSubOb())
		if type(self) is SubsObject: return tuple([None if k==None else k.obj.isSubOb() for k in self.subs])
		if type(self) is Lambda:
			def sah(k):
				if type(k) is tuple: return tuple(sah(h) for h in k)
				if type(k) is bool: return k
				if type(k) is int: adi = []
				if type(k) is Inspection:
					if k.root<self.verdepth: return k
					adi = k.inspect
					k = k.root
				if type(k) is int:
					if k<self.verdepth: return k
					else:
						# def und(mog,k):
						# 	if type(mog) is not list:
						# 		if k==0: return []
						# 		return k-1
						# 	else:
						# 		for m in range(len(mog)):
						# 			u = und(mog[m],k)
						# 			if type(u) is list: return [m]+u
						# 			else: k = u
						# 		return k
						# return und(self.si,k-self.verdepth)+adi
						return [k-self.verdepth]+adi
				return [k[0]+len(self.si)]+k[1:]
			return sah(self.obj.isSubOb())

		if type(self) is RefTree and self.core!=None:
			k = self.core.isSubOb()
			if self.args!=None and type(k) is list:
				if k[0]<len(self.args.subs):
					return self.args.deepreference(k).isSubOb()
				else:
					return [k[0]-len(self.args.subs)]+k[1:]
			return k
		if type(self) is RefTree:
			if self.src==None: return self.name
			else:
				k = self.src.isSubOb()
				if type(k) is list:
					return k+[self.name]
				if type(k) is tuple:
					return k[self.name]
				if type(k) is int:
					return Inspection(k,[self.name])
				if type(k) is Inspection:
					return Inspection(k.root,k.inspect+[self.name])
				print("==="*8)
				print(k)
				print(type(self.src))
				print(type(self.src.core))
				print(type(self.src.core.core))
				print(self.src.core.core)
				print(self.name)
				print()
				# print(self.src.prepr(FormatterObject(None,fullrepresent=True),[]))
				print(type(k))
				assert False
		return False


def initTobj(F):
	indbg=[False]
	def _dbgTest():
		indbg[0]=True

	def wrapper(self,*args,**kwargs):
		"""dbg_ignore"""
		F(self,*args,**kwargs)
		if "verdepth" in kwargs:
			self.setSafety(self.verdepth)
	if indbg[0]: return wrapper
	return F
def coflattenunravel(si,ob,left):
	# def _dbgTest():
	# 	assert ob.verdepth!=None
	if type(si) is list:
		res = []
		for n in range(len(si)):
			res = res + coflattenunravel(si[n],None if ob==None else ob.reference(n),left+len(res))
		return res
	return [(left,ob)]
def longflattenunravel(si,ty,ob,left):
	if type(si) is list:
		s = 0
		res = []
		for k in range(len(si)):
			if ty[k]!=False:
				ui,left = longflattenunravel(si[k],ty[k],ob.reference(s),left)
				res = res + ui
				s+=1
			else:
				left += longcount(si[k])
		return (res,left)
	return ([(left,ob)],left+1)
def lazyflatten(F):
	def wrapper(self,delta,mog=False,assistmog=None,prep=None,obj=None,fillout=None,then=False):
		"""dbg_ignore"""

		if type(mog) is not list and type(mog) is not bool: return Tobj.flatten(self,delta,mog,assistmog,prep,obj,fillout=fillout,then=then)

		sel = self.get_si(delta)

		if type(mog) is bool and mog == False: mog = sel

		if len(sel) != len(mog):
			raise InvalidSplit()
		if assistmog == None:
			assistmog,ext = striphuman(self.verdepth+delta.lenchange,mog)
			fillout = self.verdepth+delta.lenchange

		return F(self,delta,mog,assistmog,prep,obj,fillout,then=then)
	return wrapper



def compassionate_reshift(nty,delta,cuweird):
	def _dbgExit(outp):
		outp.setSafety(nty.verdepth-len(cuweird))
	if len(delta)==0: return nty
	# if len(delta) 
	# print("compassionate_reshifting... ",delta)
	nonam = []
	nosec = []
	for name,ob,ind in cuweird:
		reqind = nty.verdepth+len(nosec)-len(cuweird)
		actualind = ob.ob.verdepth+ob.srows.lenchange
		nonam.append(name)
		nosec.append(ob.dpush(ScopeDelta(([] if reqind==actualind else [(reqind-actualind,actualind)])+[(c[1],c[0],reqind,0) for c in delta[:ind] if c[1]+c[0]!=reqind])))
	try:
		return entrycomplicate(nty.dpush(ScopeDelta([(c[1],c[0],nty.verdepth,0) for c in delta if c[1]+c[0]!=nty.verdepth])),nosec,names=nonam)# <><><><> this is broke
	except Exception as u:
		print("CONTAIN")
		print("\t",nty.verdepth)
		print("\t",nty.prepr(FormatterObject(None,printcomplicators=True,littleeasier=False),[]))
		print("\t",nty.prepr(FormatterObject(None,printcomplicators=True,fullrepresent=True,littleeasier=False),[]))
		print("\t",ScopeDelta([(c[1],c[0],nty.verdepth,0) for c in delta]))
		raise u


class DualSubs(Tobj):

	def __eq__(self,other):
		return type(other) is DualSubs and self.rows == other.rows
	def __hash__(self):
		if self.cachehash != None: return self.cachehash
		self.cachehash = hash(tuple(self.rows))
		return self.cachehash
	@initTobj
	def __init__(self,rows=None,verdepth=None,origin =None,pos=None):
		self.rows = rows if rows != None else []
		self.origin = origin
		self.verdepth = verdepth
		self.cachehash = None
		# self.erased = [] if erased==None else erased
		transferlines(self,pos)
		def _dbgTest():
			# if self.verdepth!=None:
			# 	for a in range(len(self.rows)):
			# 		if self.rows[a].obj==None:
			# 			for b in range(a+1,len(self.rows)):
			# 				if hasattr(self.rows[b].type,'alsubbedsafety'):
			# 					assert self.rows[a].type.verdepth not in self.rows[b].type.alsubbedsafety

			for k in self.rows:
				assert type(k) is TypeRow
				if self.verdepth!=None:
					assert not hasfixes(k.name)


	def preprot_fordebug(self):
		return ScopeDelta([([(self.verdepth+r,None) for r in range(len(self.rows)) if self.rows[r].obj==None],)])

	def extractbetween(self,older,hiju=None,blame=None):#this one is better if it just does the dpush flat out
		for j in self.rows:
			if j.obj==None:
				raise LanguageError(blame,"Incomplete specification of function call.")

		# cu = []
		cuu = []
		left = 0
		for g in range(len(self.rows)):
			if older.rows[g].obj == None:
				jah = self.rows[g].obj.dpush(ScopeDelta([(-left,self.verdepth)])) if left else self.rows[g].obj
				if hiju!=None: jah = entrycomplicate(jah,hiju[0],names=hiju[1])
				cuu.append(SubRow(None,jah))
				# cuu.append(SubRow(None,complicate(self.rows[g].obj,cu)))
			left += longcount(older.rows[g].name)
		return cuu

	def isemptytype(self):
		return len(self)==0


	def writefile(self,file,shutup=False):
		if not shutup:
			if self.origin ==None: file.writeChar("C")
			else:
				file.writeChar("D")
				self.origin[0].writefile(file)
				file.writeNumInc(self.origin[1])
				file.writeNumInc(self.origin[2])
		file.writeNum(len(self.rows))
		for j in self.rows:
			j.writefile(file)

	def prepr(self,context,trail):
		if context.shouldtrim(trail) and any(row.obj!=None for row in self.rows) and self.verdepth!=None:
			return self.trimallnonessential().prepr(context,trail)
		yud = []
		for k in range(len(self.rows)):
			word = context.newcolors(self.rows[k].name)
			yud.append(self.rows[k].prepr(context,trail+[k],word=word))
			context = context.addbits(word)
		return context.red("{")+",".join(yud)+context.red("}")+context.clickable(trail)
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		if context.shouldtrim(trail) and any(row.obj!=None for row in self.rows) and self.verdepth!=None:
			return self.trimallnonessential().pmultiline(context,trail,out,indent,prepend,postpend,callback)
		pmultilinecsv(context,trail,out,indent,self.rows,prepend+context.red("{"),context.red("}")+context.clickable(trail)+postpend,lamadapt=lambda n,x:x.name,callback=callback,delim=context.red(","))

	def detect(self,ranges,worrynot=False):
		# if light:
		if any(row.detect(ranges) for row in self.rows): return True

		# else:
		# 	if any(row.obj==None and row.detect(ranges) for row in self.rows): return True
		if not worrynot and hasattr(ranges,'precal'): ranges.precal = [a for a in ranges.precal if a<self.verdepth]
		return False

	def look(self,result,worrynot=False,lowerbound=False):
		for row in self.rows: row.look(result,lowerbound=lowerbound)
		if not worrynot:
			for i in range(self.verdepth,self.verdepth+longcount(self)): result.discard(i)
			# for i in result:
			# 	if i>=self.verdepth: result.remove(i)
	def advlook(self,result,pushes,worrynot=False,lowerbound=False):
		for row in self.rows: row.advlook(result,pushes,lowerbound=lowerbound)
		if not worrynot:
			for i in range(self.verdepth+pushes.lenchange,self.verdepth+pushes.lenchange+longcount(self)):
				result.discard(i)
			# if hasattr(pushes,'lookmemo'):
			for i in range(self.verdepth,self.verdepth+longcount(self)):
				pushes.lookmemo.discard(i)
			# for i in result:
			# 	if i>=self.verdepth: result.remove(i)




	# def changeVD(self,amt):
	# 	return DualSubs([row.changeVD(amt) for row in self.rows],self.verdepth+amt,None if self.origin==None else (self.origin[0].changeVD(amt),self.origin[1],self.origin[2]))
	def simpush(self,alo):
		short = alo.mem2.get(id(self));
		if short!=None: return short
		res = DualSubs([a.simpush(alo) for a in self.rows],verdepth=self.verdepth+alo.amt,origin=None if self.origin==None else (self.origin[0].simpush(alo),self.origin[1],self.origin[2]),pos=self)
		alo.mem2[id(self)] = res
		return res

	def hascorrectlinks(self,yooj={},isolate=True):
		if isolate: yooj = copy.copy(yooj)
		sof = self.verdepth
		for j in range(len(self.rows)):
			self.rows[j].type.hascorrectlinks(yooj)
			nsof = sof+longcount(self.rows[j].name)
			if self.rows[j].obj!=None:
				self.rows[j].obj.hascorrectlinks(yooj)
				def lambchop(l,si,rsu):
					if type(si) is not list: yooj[l] = rsu
					else:
						for i in range(len(si)):
							lambchop(l,si[i],inspectref(rsu,[i]))
							l+=longcount(si[i])
				lambchop(sof,self.rows[j].name,self.rows[j].obj.isSubOb())
			else:
				for k in range(sof,nsof): yooj[k] = None
			sof = nsof

			# inspectref(root,path)

# inspection intanglement lmao<><> make sure inspections are immutable.


	def canbetranslated(self,pushes):
		# ScopeDelta([([(self.verdepth+r,None) for r in range(len(self.rows)) if self.rows[r].obj==None],)])


		if alreadycanbetranslated(self,pushes): return
		aid = ScopeDelta()
		sof = self.verdepth
		for j in range(len(self.rows)):
			self.rows[j].type.canbetranslated(aid+pushes)
			nsof = sof+longcount(self.rows[j].name)
			if self.rows[j].obj!=None: self.rows[j].obj.canbetranslated(aid+pushes)
			else:
				aid = aid+ScopeDelta([([(k,None) for k in range(sof,nsof)],)])
			sof = nsof
		if self.origin!=None: 
			self.origin[0].canbetranslated(pushes)


	def dpush(self,pushes,exob=None,frozen=False,selective=None,worrynot=False):
		early = pushes.getmemo(self,exob,False)
		if early!=None: return early
		left = 0
		cu = [row.dpush(pushes) for row in self.rows]
		if not worrynot and hasattr(pushes,'delaymemo'):
			for k in range(self.verdepth+pushes.lenchange,self.verdepth+pushes.lenchange+longcount(self)):
				pushes.delaymemo.pop(k,None)
			# pushes.delaymemo = {k:v for (k,v) in pushes.delaymemo.items() if k<self.verdepth+pushes.lenchange}
		passor = None
		if self.origin!=None: passor = (self.origin[0].dpush(pushes),self.origin[1],self.origin[2])
		# faedebug = str([a.type.alsubbedsafety if hasattr(a.type,'alsubbedsafety') else None for a in self.rows])
		# try:
		res = DualSubs(cu,verdepth=self.verdepth+pushes.lenchange,origin=passor,pos=self)
		# except AssertionError:
		# 	print("   HIT")
		# 	print(self.verdepth,len(self.rows))
		# 	print([a.type.alsubbedsafety if hasattr(a.type,'alsubbedsafety') else None for a in self.rows])
		# 	print(faedebug)
		# 	print([a.obj==None for a in self.rows])
		# 	print(pushes)
		# 	assert False
		pushes.setmemo(self,exob,False,res)
		return res

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None,keepr=False,advanced=None):
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else other.correction()+rigpush)
		if type(other) is RefTree:
			att = other.mangle_UE()
			if att!=None: return self.compare(att,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not DualSubs: return False
		if len(self) == len(other): advanced = None
		if len(self) < len(other) and advanced==None: return False
		if len(self) > len(other): return False
		if lefpush == None: lefpush = ScopeDelta()
		if rigpush == None: rigpush = ScopeDelta()
		if not keepr:
			lefpush = lefpush.isolate()
			rigpush = rigpush.isolate()
		lk = 0
		rk = 0
		dsc = self.verdepth + lefpush.lenchange
		while lk<len(self.rows) or rk<len(other.rows):
			if lk<len(self.rows) and self.rows[lk].obj != None:
				jl = longcount(self.rows[lk].name)
				lefpush.append((-jl,dsc))
				lk += 1
			if lk==len(self.rows) and advanced!=None:
				while rk<len(other.rows):
					advanced.append(other.rows[rk])
					rk+=1
			if rk<len(other.rows) and other.rows[rk].obj != None:
				jr = longcount(other.rows[rk].name)
				rigpush.append((-jr,dsc))
				rk += 1
			if lk<len(self.rows) and rk<len(other.rows) and self.rows[lk].obj==None and other.rows[rk].obj==None:
				if not conservativeeq(self.rows[lk].name,other.rows[rk].name): return False

				if not self.rows[lk].type.compare(other.rows[rk].type,odsc,thot,extract,lefpush,rigpush): return False
				j = longcount(self.rows[lk].name)
				dsc += j
				lk += 1
				rk += 1
		return True
	def append(self,other):
		return DualSubs(self.rows+[other],verdepth=self.verdepth)
	def __add__(self,other):
		return DualSubs(self.rows+other.rows,verdepth=self.verdepth)
	def __len__(self):
		return len([k for k in self.rows if k.obj == None])
	def __getitem__(self, key):
		return [k for k in self.rows if k.obj == None][key].type
	def semavail(self,mog=False):
		if mog == False: mog = self.get_si()
		return [self.rows[k].type.semavail(mog[k]) if type(mog[k]) is list else mog[k] for k in range(len(self.rows)) if self.rows[k].obj == None]

	def trimallnonessential(self,si=None,disgrace=None):
		return self.innertrim(si=si,disgrace=disgrace)
	def innertrim(self,si=None,disgrace=None):
		si = self.semavail() if si==None else si
		if conservativeeq([a.name for a in self.rows],si): return self
		delta   = [] if disgrace == None else disgrace[0]
		cuweird = [] if disgrace == None else disgrace[1]
		# cunames   = [] if disgrace == None else disgrace[2]
		def killcompare(si,divisibility):
			if type(si) is not list: return si
			return [si[k] if divisibility[k]==True else killcompare(k[k],divisibility[k]) for k in range(len(si)) if divisibility[k]!=False]
		def _dbgTest():
			if type(si) is list:
				assert len(si)==len(self.semavail())
		left = self.verdepth
		cu = []
		s = 0
		brap = self.get_divisibility_si()
		for k in range(len(self.rows)):
			if self.rows[k].obj == None:
				nty = compassionate_reshift(self.rows[k].type,delta,cuweird)
				kaname = self.rows[k].name
				if s<len(si) and type(si[s]) is list:
					kaname = killcompare(self.rows[k].name,brap[k])
					nty = nty.innertrim(si[s])
				cu.append(TypeRow(kaname,nty,None,self.rows[k].silent))
				s += 1
			# chdelta = ScopeDelta([(c[1],c[0],left,0) for c in delta])
			# for i in self.rows[k].ripsingle(): cusecrets.append(i.dpush(chdelta))
			# delta.append((longcount(self.rows[k].name),left))
			if type(self.rows[k].name) is not list:
				# assert type(si[s-1]) is not list
				if self.rows[k].obj!=None:
					# chdelta = ScopeDelta([(c[1],c[0],left,0) for c in delta])
					cuweird.append((self.rows[k].name,DelayedComplication(self.rows[k].obj),len(delta)))
					# cunames.append(self.rows[k].name)
					delta.append((1,left-sum(a[0] for a in delta)))
					# def _dbgTest():
					# 	# assert longcount(self.rows[k].name)==1
					# 	# assert len(cuweird)-1==longcount(self.semavail()[:s])-longcount([n.name for n in self.rows[:k]])
					# 	# assert longcount(self.rows[k].name)+longcount([n.name for n in self.rows[:k]])==longcount([n.name for n in self.rows[:k+1]])
					# 	# print([a.name for a in self.rows])
					# 	# print(self.semavail())
					# 	# print(s,k)
					# 	# print(len(cuweird))
					# 	# print(longcount(self.semavail()[:s])-longcount([n.name for n in self.rows[:k+1]]))
					# 	assert -len(cuweird)==longcount(self.semavail(si)[:s])-longcount([n.name for n in self.rows[:k+1]])
				# else:
				# 	assert type(si[s-1]) is not list

				# def _dbgTest():
				# 	assert -len(cuweird)==longcount(self.semavail(si)[:s])-longcount([n.name for n in self.rows[:k+1]])
				# assert False
			elif not conservativeeq(self.rows[k].type.get_sem_si(self.rows[k].name),self.rows[k].name) or self.rows[k].obj!=None:
				muz = self.rows[k].type.flatten(ScopeDelta(),self.rows[k].name,obj=None if self.rows[k].obj==None else DelayedComplication(self.rows[k].obj)).flat
				if self.rows[k].obj!=None:
					# chdelta = ScopeDelta([(c[1],c[0],left,0) for c in delta])
					for m in muz:
						cuweird.append((m.name,m.obj,len(delta)))
						# cusecrets.append(m.obj)
						# cunames.append(m.name)
					delta.append((len(muz),left-sum(a[0] for a in delta)))
					# def _dbgTest():
					# 	assert -len(cuweird)==longcount(self.semavail(si)[:s])-longcount([n.name for n in self.rows[:k+1]])
				else:
					def unshift(recleft,brap,old,new):
						if type(old) is not list: return recleft+1
						# assert False
						sl=0
						for k in range(len(brap)):
							yat = longcount(old[k])
							if brap[k]==False:
								# print("brap...")
								tdep = muz[recleft].obj.ob.verdepth + muz[recleft].obj.srows.lenchange
								# chdelta = ScopeDelta(([] if tdep==corrent[0] else [(corrent[0]-tdep,corrent[0])]) + [(c[1],c[0],corrent[0],0) for c in delta])
								for m in muz[recleft:recleft+yat]:
									cuweird.append((m.name,m.obj,len(delta)))
									# cusecrets.append(muz[i].obj)#.dpush(chdelta))
									# cunames.append(muz[i].name)
								delta.append((yat,tdep-sum(a[0] for a in delta)))
								# corrent[0] += yat
							else:
								if type(new[sl]) is list: unshift(recleft,brap[k],old[k],new[sl])
								sl+=1
							recleft += yat
						return recleft
					unshift(0,brap[k],self.rows[k].name,si[s-1])
					# def _dbgTest():
					# 	assert -len(cuweird)==longcount(self.semavail(si)[:s])-longcount([n.name for n in self.rows[:k+1]])
			# else:
			# 	def _dbgTest():
			# 		assert longcount(self.rows[k].name)==longcount(self.semavail(si)[s-1])
			left += longcount(self.rows[k].name)
		# 	def _dbgTest():
		# 		assert left == self.verdepth+longcount([n.name for n in self.rows[:k+1]])
		# 		assert -len(cuweird)==longcount(self.semavail(si)[:s])-longcount([n.name for n in self.rows[:k+1]])
		# def _dbgTest():
		# 	assert -len(cuweird)==longcount(self.semavail(si))-longcount(self)
		return DualSubs(cu,verdepth=self.verdepth)


	@lazyflatten
	def flatten(self,delta,mog,assistmog,prep=None,obj=None,fillout=None,then=False):
		# def _dbgTest():
		# 	self.canbetranslated(ScopeDelta())
		s = 0
		cu = ScopeObject()
		left = self.verdepth + delta.lenchange
		for n in range(len(self.rows)):
			nobj = None
			if self.rows[n].obj != None:
				nobj = DelayedComplication(self.rows[n].obj,delta)
			else:
				if obj != None:
					nobj = obj.reference(s)
				s+=1
			nflat = self.rows[n].type.flatten(delta,mog[n],assistmog[n],prep,obj=nobj,fillout=fillout)
			cu.flat += nflat.flat
			vv = longcount(self.rows[n].name)
			if conservativeeq(self.rows[n].name,mog[n]) and prep == None:
				if self.rows[n].obj == None and nobj!=None:
					jaaj = longflattenunravel(self.rows[n].name,self.rows[n].type.get_divisibility_si(),nobj.observe(),left)
					delta = delta + ScopeDelta([(jaaj[0],)])
				elif fillout!=left:
					delta = delta + ScopeDelta([(fillout,0,left,vv)])
				left += vv
			else:
				delta = delta + ScopeDelta([(len(nflat.flat),fillout)])
				left += len(nflat.flat)
				if self.rows[n].obj == None:
					if nobj == None:
						dbgdbg = left
						passprep = prep.emptyinst(dbgdbg,striphuman(dbgdbg-longcount(prep),prep.get_si())[0]) if prep != None else None
						kaya = self.rows[n].type.emptyinst(dbgdbg,assistmog[n],prep=passprep)
					else:
						kaya = nobj.observe()
					jaaj = longflattenunravel(self.rows[n].name,self.rows[n].type.get_divisibility_si(),kaya,left)
					delta = delta + ScopeDelta([(jaaj[0],)])
				delta = delta + ScopeDelta([(-vv,left)])
			fillout = fillout + len(nflat.flat)
		return (cu,delta) if then else cu

	def inheritpopulate(self,mapping,obj,fullmapping,upgrades):
		s = 0
		cu = []
		ncu = []
		delta = ScopeDelta()
		left = 0
		for n in range(len(self.rows)):
			oldelta = delta
			if self.rows[n].obj == None:
				# if type(obj.isSubOb()) is tuple:
				# 	print("\n\nREFERENCING: ",obj.prepr(FormatterObject(None,fullrepresent=True,printcomplicators=True)))
				cobj = obj.reference(s)
				s+=1
				jaaj = longflattenunravel(self.rows[n].name,self.rows[n].type.get_divisibility_si(),cobj,self.verdepth+left)
				delta = delta + ScopeDelta([(jaaj[0],)])
				nobj = DelayedComplication(cobj,ScopeDelta([] if left==0 else [(left,self.verdepth)]))
			else:
				nobj = DelayedComplication(self.rows[n].obj,delta)


			si = self.rows[n].name
			def coresp(l,m,k):
				if type(m) is not list:
					if l!=m: return None
					return upgrades.get(k,0)
				for g in m:
					du = coresp(l,g,k)
					if du!=None: return du
					k = k+longcount(g)
			if type(si) is not list:
				amt = coresp(left,fullmapping,0)
				if amt != 0 and amt!=None:
					ty = self.rows[n].type if oldelta.isempty() else self.rows[n].type.dpush(oldelta)
					# ty = complicate(ty,[DelayedComplication(c) for c in cu])
					nobj = DelayedComplication(reparent(ty,amt,nobj.observe()))
				cu.append(nobj)
				ncu.append(si)
			else:
				# ty = self.rows[n].type if oldelta.isempty() else self.rows[n].type.dpush(oldelta)
				if conservativeeq(self.rows[n].type.get_sem_si(si,oldelta),si) and not any(k in upgrades for k in range(left,left+longcount(si))):
					abj = shortwidereferencerecurse(nobj,si)
					cu = cu + abj[0] + [abj[s].simpush(SimpleDelta(s,self.verdepth+len(cu))) for s in range(1,len(abj))]
					ncu = ncu + longlist(si)
				else:
					pjast = self.rows[n].type.flatten(oldelta,si,obj=DelayedComplication(nobj)).flat
					jast = [a.obj for a in pjast]
					for k in range(len(jast)):
						amt = coresp(left+k,fullmapping,0)
						if amt!=0 and amt!=None:
							jast[l] = DelayedComplication(reparent(pjast[l].type.observe(),amt,jast[l].observe()))
					cu = cu + jast#[complicate(jast[k],[DelayedComplication(jast[l]) for l in range(k)]) for k in range(len(jast))]
					ncu = ncu + [a.name for a in pjast]


			left+=longcount(self.rows[n].name)
		return buildfrom(mapping,cu,self.verdepth,ncu)

	def emptyinst(self,limit,mog=False,prep=None):
		if mog == False: mog,limit = striphuman(limit,self.get_si())
		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)
		assert len(self.rows) == len(mog)
		mog = [mog[i] for i in range(len(mog)) if self.rows[i].obj == None]
		return SubsObject([SubRow(None,self[k].emptyinst(limit,mog[k],prep)) for k in range(len(self))],verdepth=limit)
	def needscarry(self):
		return False
	
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assertstatequal(indesc,self,carry,u_type(len(indesc)))
		outs = []
		oidns = indesc
		bi = len(indesc)
		for n in range(len(self.rows)):
			if self.rows[n].type == None:
				obj,nty = self.rows[n].obj.verify(indesc,reqtype=True)
			elif type(self.rows[n].type) is Strategy:

				gnoa,ndsid = self.rows[n].type.args.verify(indesc,then=True)
				if self.rows[n].type.type == None:
					obj,nty = self.rows[n].obj.verify(ndsid,reqtype=True)
				else:
					nty = self.rows[n].type.type.verify(ndsid,u_type(len(ndsid)))
					obj = self.rows[n].obj.verify(ndsid,nty) if self.rows[n].obj!=None else None

				nty = Strategy(gnoa,nty,verdepth=len(indesc))

				if obj!=None:#<><><> this is pretty bad... it inverse pushes everything in gnoa even though gnoa is unused.
					obj = obj.addlambdas(gnoa,pos=obj)
					# despar = ScopeDelta()
					# gnoa.trimallnonessential(None,despar)
					# obj = correctLambda(gnoa.semavail(),obj,despar,verdepth=len(indesc),pos=obj)
			else:
				nty = self.rows[n].type.verify(indesc,u_type(len(indesc)))
				obj = self.rows[n].obj.verify(indesc,nty) if self.rows[n].obj != None else None


			try:
				self.rows[n].name = fixnames(self.rows[n].name,nty.get_corrector_si())

				vertype = TypeRow(self.rows[n].name,nty,obj if obj!=None else SubsObject([],verdepth=len(indesc)) if nty.isemptytype() else None,self.rows[n].silent)
				outs.append(vertype)

				if type(self.rows[n].name) is not list:
					indesc = indesc.addflat(ScopeObject([vertype.delay()]))
				else:
					indesc = indesc.addflat(nty.flatten(ScopeDelta([]),self.rows[n].name,obj=None if vertype.obj==None else DelayedComplication(vertype.obj)))
			except InvalidSplit as u:
				raise u.reblame(self,nty,self.rows[n].name,indesc)

		outp = DualSubs(outs,pos=self,verdepth=bi)
		return (outp,indesc) if then else (outp,u_type(bi)) if reqtype else outp
	def peelcompactify(self,indesc,compyoks,then=False,earlyabort=True):
		def _dbgEnter():
			self.setVerified()
			self.setSafety(len(indesc))
			indesc.setSafety(0)
			assert type(compyoks) is list
			for j in compyoks:
				assert type(j) is tuple and (len(j) == 3 or len(j)==4)
				if j[2]==False:
					j[1].setSafety(indesc.beginlen())
				else:
					j[1].setSafety(len(indesc))


		# def _dbgExit(outp):
		# 	if outp != None:
		# 		if then:
		# 			outp,ninds = outp
		# 			assert type(ninds) is ScopeObject
		# 			ninds.setSafety(0)
		# 		outp,early = outp
		# 		assert type(early) is bool
		# 		assert type(outp) is DualSubs
		# 		outp.setVerified()
		# 		outp.setSafety(len(indesc))


		compyoks = copy.copy(compyoks)
		while True:
			try:
				return self.compacrecurse(compyoks,[],[],indesc,ScopeDelta([]),then=then,earlyabort=earlyabort)
			except RestartCompactify as u: earlyabort = u.earlyabort
			# except AssertionError:
			# 	print([a.type.alsubbedsafety if hasattr(a.type,'alsubbedsafety') else None for a in self.rows])
			# 	print([(a.type.verdepth,a.obj==None) for a in self.rows])
			# 	assert False

	def compacassign(self,inyoks,overflow=None,cosafety=None):
		prev = False
		for g in inyoks:
			if g[0] != None: prev = True
			elif prev: raise LanguageError(self,"positional argument may not follow keyword argument.")
		def firstnamed(spoken,labels,car,mot=None,blame=None,name=None):
			# more prots
			mot = car.get_si() if mot == None else mot
			for f in range(len(mot)):
				if car.rows[f].obj != None: continue
				if spoken[f] == True: continue

				if mot[f] == labels[0] or (labels[0] == None and ((cosafety!=None and f<cosafety) or (car.rows[f].silent==None or not car.rows[f].silent['silent']))):
					if len(labels) == 1:
						spoken[f] = True
						return [f]
					nxc = car.rows[f].type.type if type(car.rows[f].type) is Strategy else car.rows[f].type

					if type(car.rows[f].type) is not DualSubs:
						raise LanguageError(blame,"Tried to subaccess thing that doesn't have subproperties "+str(name))

					if spoken[f] == False: spoken[f] = [False]*len(nxc)
					k = firstnamed(spoken[f],labels[1:],nxc)
					if k: return [f]+k
				elif isinstance(mot[f],list):
					if spoken[f] == False: spoken[f] = [False]*len(mot[f])
					k = firstnamed(spoken[f],labels,car.rows[f].type,mot[f],blame=blame,name=name)
					if k: return [f] + k
		def fullp(spoken):
			if spoken == False: return False
			return spoken == True or all(fullp(k) for k in spoken)
		spoken = [False]*len(self.rows)
		yoks = []
		for s in range(len(inyoks)):
			nan = firstnamed(spoken,[None] if inyoks[s][0] == None else inyoks[s][0],self,blame=inyoks[s][1][0],name=inyoks[s][0])
			if nan == None:
				# if safety != None and s < safety:
				# 	raise VariableAssignmentError(inyoks[s][1][0],inyoks[s][0])
				overflow.append(inyoks[s])
			else:
				yoks.append((nan,inyoks[s][1][0],inyoks[s][1][1]))
		return yoks
	def compacrecurse(self,yoks,trail,prep,indesc,delta,then=False,earlyabort=False):
		def _dbgEnter():
			indesc.setSafety(0)
			assert type(yoks) is list
			for j in yoks:
				assert type(j) is tuple
				if j[2]==False:
					j[1].setSafety(indesc.beginlen())
				else:
					j[1].setSafety(len(indesc)-len(prep))
			self.setVerified()
			self.setSafety(len(indesc))
		def _dbgExit(outp):
			if then:
				outp,(ninds,ndelt) = outp
				assert type(ninds) is ScopeObject
				assert type(ndelt) is ScopeDelta
				ninds.setSafety(0)
			outp,early = outp
			assert type(early) is bool
			assert type(outp) is DualSubs
			outp.setVerified()
			outp.setSafety(len(indesc))
			for c in yoks:
				if c[2]==False: assert False
		def getming(thot,st):
			ming = None;
			for regrab in yoks[st:len(yoks)]:
				if ming == None:
					ming = regrab[0]
					continue
				for i in range(min(len(ming),len(regrab[0]))):
					if regrab[0][i]<ming[i]:
						ming = regrab[0]
						break
			return ming
		def namerical(lim,names,sof):
			if type(names) is not list: return [(lim,sof)]
			i = []
			for j in range(len(names)):
				i = i+namerical(lim+len(i),names[j],sof+[j])
			return i
		# secretcu = []
		cu = []
		thot = prep
		for n in range(len(self.rows)):
			row = self.rows[n]
			rowtype = row.type.dpush(delta)
			if self.rows[n].obj != None:
				obj = self.rows[n].obj.dpush(delta) 
			else:
				obj = None
				lentotal = len(indesc)
				lentho   = len(thot)
				lencom1  = lentotal - lentho
				# def _dbgTest():
				# 	assert len(secretcu) == lentho
				try:
					for k in range(len(yoks)):
						if yoks[k][0] == trail+[n]:
							if yoks[k][2] != False:
								if yoks[k][2] != True:
									st = len(yoks)
									othertype = yoks[k][2].simpush(SimpleDelta(lentho,lencom1)) if lentho else yoks[k][2]
									obj       = yoks[k][1].simpush(SimpleDelta(lentho,lencom1)) if lentho else yoks[k][1]
									obj = implicitcast(indesc,rowtype,othertype,obj,blame=yoks[k][1],soften=earlyabort,extract=yoks,thot=thot,odsc=lencom1,owner=trail+[n])
									yoks[k] = (yoks[k][0],obj.dpush( ScopeDelta([(-lentho,lencom1)])) if lentho else obj,True)
									# yoks[k] = (yoks[k][0],complicate(obj,secretcu),True)
									ming = getming(thot,st)
									if ming!=None: raise RestartCompactify(earlyabort)
								else:
									obj = yoks[k][1].simpush(SimpleDelta(lentho,lencom1)) if lentho else yoks[k][1]
								if lentho and rowtype.detect(ScopeDelta([(-lentho,lencom1)])): raise CouldNotDeduceType(yoks[k][1]).soften(earlyabort)
								break
							if lentho and rowtype.detect(ScopeDelta([(-lentho,lencom1)])):
								if type(yoks[k][1]) is Lambda and not yoks[k][1].obj.needscarry():
									try:
										truncargs,ntype = rowtype.extractfibration(indesc,yoks[k][1].si,blame=yoks[k][1])
									except InvalidSplit as u:
										raise u.soften(earlyabort)
									if not lentho or not truncargs.detect(ScopeDelta([(-lentho,lencom1)])):
										yfactor = indesc.addflat(truncargs.flatten(ScopeDelta(),yoks[k][1].si))
										earlyabort = False
										obj,ntyp = yoks[k][1].obj.verify(yfactor,reqtype=True)
										obj  =  obj.addlambdasphase2(yoks[k][1].si,pos=yoks[k][1])
										ntyp = ntyp.addfibration(truncargs)
										yoks[k] = (yoks[k][0],obj.dpush( ScopeDelta([(-lentho,lencom1)])) if lentho else obj,True)
										st = len(yoks)
										obj = implicitcast(indesc,rowtype,ntyp,obj,blame=yoks[k][1],soften=earlyabort,extract=yoks,thot=thot,odsc=lencom1,owner=trail+[n])
										ming = getming(thot,st)
										if ming!=None: raise RestartCompactify(earlyabort)
										raise CouldNotDeduceType(yoks[k][1]).soften(earlyabort)
								break
							earlyabort = False
							obj = yoks[k][1].verify(indesc,rowtype)
							yoks[k] = (yoks[k][0],obj.dpush( ScopeDelta([(-lentho,lencom1)])) if lentho else obj,True)
							# yoks[k] = (yoks[k][0],complicate(obj,secretcu),True)
							break
				except LanguageError as u:
					raise u.addparameterdata(yoks,trail+[n],len(thot),rowtype,indesc)
			if any(len(o[0])>len(trail)+1 and o[0][:len(trail)+1] == trail+[n] for o in yoks):
				assert obj == None
				moro,earlyabort = rowtype.compacrecurse(yoks,trail+[n],thot,indesc,delta,then=False,earlyabort=earlyabort)
				obj = SubsObject([],verdepth=len(indesc)) if moro.isemptytype() else None
				cu.append(TypeRow(row.name,moro,obj,self.rows[n].silent))
			else:
				cu.append(TypeRow(row.name,rowtype,obj,self.rows[n].silent))
			thot = thot+namerical(len(indesc),self.rows[n].name,trail+[n])
			if type(self.rows[n].name) is not list:
				insf = TypeRow(self.rows[n].name,rowtype,obj,self.rows[n].silent)
				if obj!=None and self.rows[n].obj == None: delta = delta + ScopeDelta([([(len(indesc),obj)],)])
				indesc = indesc.sneakadd(ScopeObject([insf.delay()]))
			else:
				if obj!=None and self.rows[n].obj == None: delta = delta + ScopeDelta([(longflattenunravel(self.rows[n].name,rowtype.get_divisibility_si(),obj,len(indesc))[0],)])
				indesc = indesc.sneakadd(self.rows[n].type.flatten(ScopeDelta([]),self.rows[n].name,obj=DelayedComplication(obj)))
		for n in range(len(self.rows)):
			for yok in yoks:
				if yok[0] == trail+[n] and cu[n].obj==None:
					raise CouldNotDeduceType(yok[1]).addparameterdata(yoks,trail+[n],len(thot),None,indesc).soften(earlyabort)
		outp = DualSubs(cu,verdepth=self.verdepth,pos=self)
		return ((outp,earlyabort),(indesc,delta)) if then else (outp,earlyabort)

	def applytemplate(self,indesc,NSC,subs,rows,blame=None,shortname=None,secret=None):
		# def _dbgTest():
		# 	self.canbetranslated(ScopeDelta())
		poppo = [(NSC[0][a],NSC[1][a]) for a in range(len(NSC[0]))]
		inc = []
		def triplecopy(ma):
			res = []
			for si,comp in ma:
				if type(si) is list:
					if len(comp[0])!=len(si): raise InvalidSplit()
					res.append(triplecopy([(si[s],comp[0][s]) for s in range(len(si))]))
				else:
					for swap in range(len(poppo)):
						if poppo[swap][0]==si:
							kres = fixnames(poppo[swap][1],comp)
							for j in range(longcount(kres)):
								inc.append(True)
							del poppo[swap]
							res.append(kres)
							break
					else:
						inc.append(False)
						res.append(si)
			return res


		def secretoken(secret,wlist,stdep,endep,tail=None):
			acu = []
			for w in range(len(wlist)):
				# tvd = wlist[w][0]
				def _dbgTest():
					wlist[w][0].setSafetyrow(stdep+w)
				ka = wlist[w][0].dpush(ScopeDelta([(endep-stdep,stdep+w)]))
				if ka.obj==None: acu.append(DelayedTypeRow(ka.name,ka.type,DelayedComplication(RefTree(stdep+w,verdepth=endep+w)),ka.silent))
				else: acu.append(ka)
			if tail!=None: acu.append(tail.simpush(SimpleDelta(len(acu),endep)))

			sj = DelayedTypeRow(secret[1],DelayedComplication(DualSubs([a.observe() for a in acu],verdepth=self.verdepth+len(wlist))),DelayedComplication(SubsObject([],verdepth=self.verdepth+len(wlist))))
			if secret[0]!=None:
				return secretoken(secret[0][0],secret[0][1],stdep-len(wlist),endep,tail=sj)
			return sj
	

		NANms = triplecopy([(a.name,a.type.get_corrector_si()) for a in self.rows])
		for pop in range(len(poppo)): raise LanguageError(blame,"cannot complete renaming statement: "+poppo[pop][0]+" was not found.")

		wlist = self.flatten(ScopeDelta([]),NANms).flat
		wonk = indesc.addflat(ScopeObject(wlist)).prepushPR(ScopeDelta([(1,indesc.beginlen()+n) for n in range(len(wlist)) if not inc[n]]))

		# print("templating:",NANms)
		jmore = DualSubs(rows,pos=blame).verify(wonk).flatten(ScopeDelta([])).flat

		wclist = [((wlist+jmore)[d],(inc+[True for j in jmore])[d],self.verdepth+d,[]) for d in range(len(inc)+len(jmore))]
		# print("BEGINBEGINBEGINBEGIN+_+_+_+_+_+_+_+_+_+_+_+_+_")

		for a in range(len(wclist)):
			lowerbound=set()
			upperbound=set()
			wclist[a][0].look(lowerbound,lowerbound=True)
			wclist[a][0].look(upperbound,lowerbound=False)
			for b in reversed(range(a)):
				# if self.verdepth+b in look:
				# 	if "meet_CLOSURE"==wclist[a][0].name:
				# 		print(wclist[a][0].name,"natively and initially found to reference:",wclist[b][0].name)
				# if "old_meet_ASSOCIATIVE"==wclist[a][0].name and self.verdepth+b==107:
				# 	print("\t",wclist[b][0].name)
				# 	print()

				# if self.verdepth+b in upperbound and self.verdepth+b not in lowerbound:
				# 	print("cannot determine if ",wclist[a][0].name,"references",wclist[b][0].name)


				if self.verdepth+b in upperbound and self.verdepth+b not in wclist[a][3]:

					if self.verdepth+b in lowerbound:
						if wclist[b][0].obj==None: wclist[a][3].append(self.verdepth+b)
						for c in wclist[b][3]:
							if c not in wclist[a][3]:
								wclist[a][3].append(c)


					elif wclist[b][0].obj==None and wclist[a][0].detect(ScopeDelta([(-1,self.verdepth+b)])):

						print("cannot determine (1) if ",wclist[a][0].name,"references",wclist[b][0].name)

						wclist[a][3].append(self.verdepth+b)
						for c in wclist[b][3]:
							if c not in wclist[a][3]:
								wclist[a][3].append(c)
					else:
						for c in wclist[b][3]: upperbound.add(c)



		def shape1(wclist,a):
			# global global_debugging
			tub = []
			wlist = []
			sources = []
			for b in range(len(wclist)):
				if b!=a and wclist[a][2] not in wclist[b][3]:
					wlist.append((wclist[b][0].dpush(ScopeDelta(copy.copy(tub))),wclist[b][1],wclist[b][2],wclist[b][3]))
					sources.append(b)
				else:
					tub.insert(0,(-1,self.verdepth+b))
			return (sources,wlist)
		def addrefs(wclist,sources,a,token):
			hs = self.verdepth
			lowerbound=set()
			upperbound=set()
			token.look(lowerbound,lowerbound=True)
			token.look(upperbound,lowerbound=False)


			for b in sources:
				if wclist[b][2] not in wclist[a][3] and wclist[a][2] not in wclist[b][3]:


					# if hs in upperbound and hs not in lowerbound:
					# 	print("cannot determine (secondary) if ",wclist[a][0].name,"references",wclist[b][0].name)


					if wclist[b][0].obj==None and hs in upperbound and (hs in lowerbound or token.detect(ScopeDelta([(-1,hs)]))):
						if hs not in lowerbound: print("cannot determine (secondary) if ",wclist[a][0].name,"references",wclist[b][0].name)
						# assert hs in look
						# if "meet_CLOSURE"==wclist[a][0].name:
						# 	print(wclist[a][0].name,"goh:",wclist[b][0].name)
					# if wclist[b][0].obj==None and token.detect(ScopeDelta([(-1,hs)])):
						wclist[a][3].append(wclist[b][2])
						for c in wclist[b][3]:
							if c not in wclist[a][3]: wclist[a][3].append(c)
						for c in range(len(wclist)):
							if wclist[a][2] in wclist[c][3]:
								for d in wclist[a][3]:
									if d not in wclist[c][3]: wclist[c][3].append(d)
				hs+=1
		def shape2(sources,wlist,wclist,converter):
			# def _dbgTest():
			# 	yooj = {}
			# 	self.verdepth=
			# 	for v in range(len(wclist)):

					# wclist[v][0].canbetranslated(ScopeDelta([([(self.verdepth+x,None) for x in range(v) if wclist[x][0].obj==None],)]))


			assert len(sources)==len(wlist)
			for b in range(len(wclist)):
				if b not in sources: sources.append(b)
			assert len(sources)==len(wclist)
			for b in range(len(wlist),len(wclist)):
				tub = []
				hacakewalk = copy.copy(sources[:b])
				for c in reversed(range(b)):
					if sources[b]<sources[c]:
						tub.append((-1,self.verdepth+c))
						del hacakewalk[c]
				def _dbgTest():
					for c in sources[b+1:]:
						if sources[b]>c:
							assert False
				miR = 0
				while miR<len(hacakewalk):
					while miR<len(hacakewalk) and hacakewalk[miR]==miR: miR+=1
					if miR>=len(hacakewalk): break
					mi = miR
					for m in range(miR+1,len(hacakewalk)):
						if hacakewalk[m]<hacakewalk[mi]: mi=m
					inc=1
					while mi+inc<len(hacakewalk) and hacakewalk[mi+inc]==hacakewalk[mi]+inc: inc+=1
					# print(miR,mi,inc,"--==--", hacakewalk)
					tub.append((self.verdepth+miR,0,self.verdepth+mi,inc))
					hacakewalk = hacakewalk[:miR]+hacakewalk[mi:mi+inc]+hacakewalk[miR:mi]+hacakewalk[mi+inc:]

				def _dbgTest():
					for f in range(len(hacakewalk)-1):
						assert hacakewalk[f+1]>hacakewalk[f]
					# if any(len(k)==4 for k in tub):
					# 	assert False
				# wclist[sources[b]][0].canbetranslated(tub)
				# tub = -ScopeDelta(tub)
				# tub = tub+converter

				tub = -ScopeDelta(tub)+converter

				# tub = tub3+tub1
				# try:
					# wclist[sources[b]][0].canbetranslated(ScopeDelta([([(self.verdepth+x,None) for x in range(len(wclist)) if wclist[x][0].obj==None],)]))
					# wclist[sources[b]][0].canbetranslated(ScopeDelta())
					# wclist[sources[b]][0].canbetranslated(tub)
				wlist.append((wclist[sources[b]][0].dpush(tub),wclist[sources[b]][1],wclist[sources[b]][2],wclist[sources[b]][3]))
				# except Exception as u:
				# 	print("EXCEPTION:")
				# 	print(sources)
				# 	print(indesc.prepushes,indesc.postpushes)
				# 	print("\t",tub)
				# 	print("\t",ScopeDelta([([(self.verdepth+x,None) for x in range(len(wclist)) if wclist[x][0].obj==None],)]))
				# 	print()
				# 	print("\t",converter)
				# 	print("\t",len(indesc))
				# 	print("\t",self.verdepth)
				# 	print("\t",[a[0].name for a in wclist])
				# 	print("\t",[a[0].name for a in wlist])
				# 	print("\t",indesc.flatnamespace())
				# 	raise u
		def correctness(lis):

			for a in range(len(lis)):
				for b in range(a):
					assert lis[a][2]!=lis[b][2]

			for i in range(len(lis)):
				for a in range(len(lis[i][3])):
					for b in range(a):
						assert lis[i][3][a]!=lis[i][3][b]

				for ref in lis[i][3]:
					for j in range(i):
						if lis[j][2]==ref:
							for ref2 in lis[j][3]:
								assert ref2 in lis[i][3]
							break
					else: assert False
		# def tightcorrectness(lis):
		# 	correctness(lis)
		# 	indesc.addflat(ScopeObject([k[0] for k in lis]))
		# 	for k in range(len(lis)):
		# 		for h in range(k):
		# 			if lis[h][0].obj==None:
		# 				a = lis[k][0].obj!=None and lis[k][0].obj.detect(ScopeDelta([(-1,self.verdepth + h)]))
		# 				c = lis[k][0].type.detect(ScopeDelta([(-1,self.verdepth + h)]))
		# 				b = (lis[h][2] in lis[k][3])
		# 				if (c or a) and not b: assert False


		upgrades = []

		dn = copy.copy(subs)
		while len(dn):
			if dn[0].name!=None and dn[0].name[0] in dn: continue
			for odex in range(len(wclist)):
				a=0
				while wclist[a][2]!=odex+self.verdepth: a+=1
				if dn[0].name==None or (wclist[a][0].obj==None or len(dn[0].name)==1) and dn[0].name[0]==wclist[a][0].name:
					# everything without a ref | everything with a ref.
					sources,wlist = shape1(wclist,a)
					wonk = indesc.addflat(ScopeObject([w[0] for w in wlist])).prepushPR(ScopeDelta([(1,indesc.beginlen()+n) for n in range(len(wlist)) if not wlist[n][1]]))
					ltype = wclist[a][0].type.observeAT(self.verdepth+len(wlist))# (ScopeDelta([(len(wlist)-a,self.verdepth+a)]))

					if dn[0].name==None or len(dn[0].name)==1:
						if secret!=None:
							wonk = wonk.invisadd(ScopeObject([secretoken(secret,wlist,self.verdepth,self.verdepth+len(wlist))]))

						if wclist[a][0].obj==None:

							obob = dn[0].obj.verify(wonk,ltype)
							yarn = DelayedTypeRow(wclist[a][0].name,DelayedComplication(ltype),DelayedComplication(obob),wclist[a][0].silent)
							addrefs(wclist,sources,a,obob)
							converter = ScopeDelta([
								([(len(indesc)+len(wlist),obob)],)
							])
							wlist.append((yarn,wclist[a][1],wclist[a][2],wclist[a][3]))
							sources.append(a)
							shape2(sources,wlist,wclist,converter)
							wclist=wlist

						else:

							extract = []
							lobj = wclist[a][0].obj.observeAT(self.verdepth+len(wlist))# (ScopeDelta([(len(wlist)-a,self.verdepth+a)]))
							# lobj = wclist[a][0].obj.dpush(ScopeDelta([(len(wlist)-a,self.verdepth+a)]))

							# def _dbgTest():
							# 	assert not lobj.detect(ScopeDelta([(len(wlist)-a,self.verdepth+a)]))
							robj = dn[0].obj.verify(wonk,ltype)

							if not lobj.compare(robj,len(indesc)+len(wlist),[(len(indesc)+i,i) for i in range(len(wlist))],extract):
								raise ObjectMismatch(dn[0].obj,lobj,robj,wonk)#self,pos,expected,got,context
							gather = []
							origsources = sources
							while len(extract):
								i = 0
								while True:
									for l in range(len(extract)):
										if wlist[extract[i][0]][2] in wlist[extract[l][0]][3]:
											i = l
											break
									else: break
								r = extract[i]
								del extract[i]
								sources2,gnlist = shape1(wlist,r[0])
								try:
									takenout = r[1].dpush(ScopeDelta([( -1,len(indesc)+i) for i in reversed(range(len(origsources))) if i not in sources2]))
								except DpushError:
									raise LanguageError(blame,"Equivalence statement cannot be made true without creating a cyclic reference.")

									
								addrefs(wclist,[origsources[i] for i in sources2],sources[r[0]],takenout)
								converter = ScopeDelta([([(len(indesc)+len(gnlist),takenout)],)])

								# ltype = wclist[a][0].type.observeAT(self.verdepth+len(wlist))
								# omtype = wlist[r[0]][0].type.dpush(ScopeDelta([(len(gnlist)-r[0],self.verdepth+r[0])]))
								omtype = wlist[r[0]][0].type.observeAT(self.verdepth+len(gnlist))


								gather.append(wlist[r[0]][2])

								gnlist.append((DelayedTypeRow(wlist[r[0]][0].name,DelayedComplication(omtype),DelayedComplication(takenout),wlist[r[0]][0].silent),wlist[r[0]][1],wlist[r[0]][2],wlist[r[0]][3]))

								sources2.append(r[0])
								shape2(sources2,gnlist,wlist,converter)
								wlist=gnlist
								enext = []
								for e in extract:
									for i in range(len(sources2)):
										if sources2[i]==e[0]:
											enext.append((i,e[1]))
											break
									else: assert False
								extract = enext
								sources=[sources[i] for i in sources2]
							converter = ScopeDelta([([
								(self.verdepth + n,wlist[n][0].obj.observe()) for n in range(len(wlist)) if wlist[n][2] in gather
							],)])
							shape2(sources,wlist,wclist,converter)
							wclist=wlist
						del dn[0]
					else:

						ty = ltype.decode()
						if type(ty) is RefTree: ty = ty.mangle_UE()
						if type(ty) is not DualSubs: raise LanguageError(blame,"Tried to subaccess thing that doesn't have subproperties "+str(dn[0].name))
						desc = []
						for o in reversed(range(len(dn))):
							if dn[o].name!=None and dn[o].name[0]==wclist[a][0].name and len(dn[o].name)>1:
								desc.append(SubRow(dn[o].name[1:],dn[o].obj))
								del dn[o]
						hab = (None,wclist[a][0].name) if secret==None else ((secret,wlist),wclist[a][0].name)

						# shortname = ltype...
						# assert False
						# def _dbgTest():
						# 	karma = ScopeDelta([(self.verdepth+v,None) for v in wlist if wlist[v][0].obj==None])
						# 	print("\t\t",karma)
						# 	ltype.canbetranslated(karma)

						retype = ty.applytemplate(wonk,([],[]),desc,[],blame=blame,shortname=ltype,secret=hab)


						yarn = DelayedTypeRow(wclist[a][0].name,DelayedComplication(retype),DelayedComplication(SubsObject(verdepth=retype.verdepth)) if len(retype)==0 else None,wclist[a][0].silent)

						upgrades.append(wclist[a][2])
					
						addrefs(wclist,sources,a,retype)
						b = self.verdepth+len(wlist)
						converter = ScopeDelta([
							(1,b),
							([(
								b+1,
								implicitcast(
									None,
									ltype.simpush(SimpleDelta(1,b)),
									retype.simpush(SimpleDelta(1,b)),
									RefTree(b,verdepth=b+1)
								)
							)],),
							(-1,b+1)
						])
						wlist.append((yarn,wclist[a][1],wclist[a][2],wclist[a][3]))
						sources.append(a)
						shape2(sources,wlist,wclist,converter)
						wclist=wlist
					break
			else:
				raise VariableAssignmentError(blame,dn[0].name[0])

		def unlongcount(si,map,lc=0):#to build child out of parent
			if type(si) is list:
				res = []
				for i in si:
					k,lc = unlongcount(i,map,lc)
					res.append(k)
				return (res,lc)
			for i in range(len(map)):
				if map[i]==self.verdepth+lc: return (i,lc+1)
			assert False


		geit = unlongcount(NANms,[i[2] for i in wclist])[0]

		charm = []
		for up in upgrades:
			charm.append(up-self.verdepth)

		dengua = [i[0] for i in wclist]
		indesc.oprows.mergedeltas(dengua)
		# def _dbgTest():
		# 	for i in range(len(dengua)):
		# 		d = dengua[i]
		# 		d.canbetranslated(ScopeDelta())
		# 		print("testing: ",d.type.ob,d.type.srows)
		# 		d.type.ob.hascorrectlinks()
		# 		if d.obj!=None:
		# 			print("testing(o): ",d.obj.ob,d.obj.srows)
		# 			d.obj.ob.hascorrectlinks()

		# 		DualSubs([d.observe() for d in dengua[:i+1]],verdepth=self.verdepth,pos=blame,origin=(shortname if shortname!=None else self,geit,charm)).hascorrectlinks()



		return DualSubs([d.observe() for d in dengua],verdepth=self.verdepth,pos=blame,origin=(shortname if shortname!=None else self,geit,charm))
class SubsObject(Tobj):
	def isfrozen(self):
		return any(s==None or s.obj.isfrozen() for s in self.subs)

	def __eq__(self,other):
		return type(other) is SubsObject and [None if a==None else a.obj for a in self.subs]==[None if a==None else a.obj for a in other.subs]
	def __hash__(self):
		if self.cachehash != None: return self.cachehash
		self.cachehash = hash(tuple([None if a==None else a.obj for a in self.subs]))
		return self.cachehash

	@initTobj
	def __init__(self,subs=None,verdepth=None,pos=None):
		# def _dbgEnter():
		# 	for sub in subs:
		# 		assert type(sub) is SubRow
		self.subs = subs if subs != None else []
		self.verdepth = verdepth
		self.cachehash = None
		transferlines(self,pos)

	def writefile(self,file,shutup=False):
		if not shutup: file.writeChar("F")
		file.writeNum(len(self.subs))
		for j in self.subs:
			j.obj.writefile(file)

	def prepr(self,context,trail):
		res = context.red("(")+",".join(["EMPTY" if self.subs[k]==None else self.subs[k].prepr(context,trail+[k]) for k in range(len(self.subs))])+context.red(")")
		return res
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		pmultilinecsv(context,trail,out,indent,self.subs,prepend+context.red("("),context.red(")")+postpend,callback=callback)

	def isemptyinst(self,si,prep=None):
		if type(si) is not list: return False
		if len(si)!=len(self.subs): return False
		return all(self.subs[k].obj.isemptyinst(si[k],prep=prep) for k in range(len(si)))

	def detect(self,ranges):
		return any(sub.detect(ranges) for sub in self.subs)


	def look(self,result,lowerbound=False):
		for sub in self.subs:
			if sub!=None: sub.obj.look(result,lowerbound=lowerbound)
	def advlook(self,result,pushes,lowerbound=False):
		for sub in self.subs:
			if sub!=None: sub.obj.advlook(result,pushes,lowerbound=lowerbound)

	def simpush(self,alo):
		short = alo.mem2.get(id(self));
		if short!=None: return short
		res = SubsObject([None if a==None else SubRow(None,a.obj.simpush(alo)) for a in self.subs],verdepth=self.verdepth+alo.amt,pos=self)
		alo.mem2[id(self)] = res
		return res


	def hascorrectlinks(self,yooj={}):
		for j in self.subs:
			if j!=None: j.obj.hascorrectlinks(yooj)

	def canbetranslated(self,pushes):
		if alreadycanbetranslated(self,pushes): return
		for j in self.subs:
			if j!=None: j.obj.canbetranslated(pushes)

	def dpush(self,pushes,exob=None,frozen=False,selective=None):
		early = pushes.getmemo(self,exob,frozen)
		if early!=None: return early
		if frozen:
			res = []
			for k in range(len(self.subs)):
				if self.subs[k]==None or (selective!=None and k!=selective):
					res.append(None)
				else:
					try:
						res.append(SubRow(None,self.subs[k].obj.dpush(pushes,exob=exob)))
					except DpushError:
						res.append(None)
			res = SubsObject(res,pos=self,verdepth=self.verdepth+pushes.lenchange)
			if selective==None: pushes.setmemo(self,exob,frozen,res)
			return res
		res = SubsObject([SubRow(None,k.obj.dpush(pushes,exob=exob)) for k in self.subs],pos=self,verdepth=self.verdepth+pushes.lenchange)
		pushes.setmemo(self,exob,frozen,res)
		return res
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else other.correction()+rigpush)
		if type(other) is RefTree: return self.compare(other.unwrapOne(),odsc,thot,extract,lefpush,rigpush)
		if type(other) is not SubsObject: return False
		if len(self.subs) != len(other.subs): return False
		return all(self.subs[k].compare(other.subs[k],odsc,thot,extract,lefpush,rigpush) for k in range(len(self.subs)))
	def phase1(self,indesc):
		def _dbgEnter():
			indesc.setSafety(0)
			self.setSafety(indesc.beginlen())
		return [(s.name,(s.obj,False)) if s.obj.needscarry() else (s.name,s.obj.verify(indesc,reqtype=True)) for s in self.subs]
	def phase1_gentle(self):
		def _dbgEnter():
			self.setVerified()
		for s in self.subs: assert s.name == None
		return [(None,(s.obj,True)) for s in self.subs]
	def needscarry(self):
		return True
		# return any(k.name!=None or k.obj.needscarry() for k in self.subs)
	
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		if carry==None:  raise TypeRequiredError(self,False)
		carry = carry.decode()
		if type(carry) is not DualSubs:
			ocarry = carry.mangle_UE() if type(carry) is RefTree else None
			if type(ocarry) is not DualSubs: raise NonUnionTypeError(self,carry,indesc)
			carry = ocarry

		oflow = []
		garbo = carry.compacassign(self.phase1(indesc),overflow=oflow)
		if len(oflow): raise VariableAssignmentError(self,oflow[0][0])

		try:
			st = carry.peelcompactify(indesc,garbo,earlyabort=False)[0]
			ga = st.extractbetween(carry,blame=self)
		except LanguageError as u:
			u.callingcontext([("(Constructing element of union)",DelayedComplication(carry),indesc,None)],0)
			raise u
		return SubsObject(ga,verdepth=len(indesc),pos=self)
class Template(Tobj):
	@initTobj
	def __init__(self,src,NSC=None,rows=None,subs=None,pos=None):
		# assert type(subs) is SubsObject
		self.NSC = ([],[]) if NSC==None else NSC
		self.rows = [] if rows == None else rows
		self.subs = [] if subs == None else subs
		self.src = src
		transferlines(self,pos)
	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assert not then
		assertstatequal(indesc,self,carry,u_type(len(indesc)))
		src = self.src.verify(indesc,u_type(len(indesc)))
		osrc = src
		src = src.decode()
		if type(src) is RefTree: src = src.mangle_UE()
		if type(src) is not DualSubs:
			raise LanguageError(self,"Can only apply templating to {"+"} object.")
		if len(self.NSC[0])!=len(self.NSC[1]):
			raise LanguageError(self,"Renaming statements must have an equal number of names on both sides.")
		for k in self.NSC[0]:
			if type(k) is list: raise LanguageError(self,"You can't recursively nest renaming statements on the left.")
		outp = src.applytemplate(indesc,self.NSC,self.subs,self.rows,self,shortname=osrc)
		if reqtype: return (outp,u_type(len(indesc)))

		# assert outp.src!=None
		return outp





	def prepr(self,context,trail):
		add = []
		# if len(self.NSC[0])==0 and len(self.NSC[1])==0: add=[]
		# elif self.NSC[0]==self.NSC[1]: add = [pmultilinelist(self.NSC[0],context)]
		# else: add = [pmultilinelist(self.NSC[0],context)+"="+pmultilinelist(self.NSC[1],context)]
		return self.src.prepr(context,trail+[len(self.rows)+len(self.subs)])+"<"+",".join(add+[self.rows[k].prepr(context,trail+[k]) for k in range(len(self.rows))]+[self.subs[k].prepr(context,trail+[k+len(self.rows)]) for k in range(len(self.subs))])+">"
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		def calls(context_,out,prepend):
			pmultilinecsv(context,trail,out,indent,self.rows+self.subs,prepend+"<",">"+postpend,callback=callback)
		self.src.pmultiline(context,trail+[len(self.rows)+len(self.subs)],out,indent,prepend,"",calls)
def correctLambda(si,obj,inp,verdepth=None,pos=None):
	def smush(tok):
		if type(tok) is list:
			res = ""
			for t in tok: res = res + smush(t)
			return res
		return tok
	si = generalfix(si)
	delta = inp
	for s in range(len(si)):
		if type(si[s]) is list:
			vv = longcount(si[s])
			delta = delta + ScopeDelta([
				(1,verdepth+s),
				(coflattenunravel(si[s],RefTree(verdepth+s,verdepth=verdepth+s+1),verdepth+s+1),),
				(-vv,verdepth+s+1)
			])
	return Lambda([smush(s) for s in si],obj if delta.isempty() else obj.dpush(delta),verdepth=verdepth,pos=pos)
class Lambda(Tobj):

	def isfrozen(self):
		return self.obj.isfrozen()

	def __eq__(self,other):
		return type(other) is Lambda and conservativeeq(self.si,other.si) and self.obj==other.obj
	def __hash__(self):
		if self.cachehash != None: return self.cachehash
		self.cachehash = hash(self.obj)
		return self.cachehash

	@initTobj
	def __init__(self,si,obj,verdepth=None,pos=None):
		self.si = si
		# assert len(si)>0
		self.obj = obj
		self.verdepth = verdepth
		self.cachehash = None
		transferlines(self,pos)
		def _dbgTest():
			if verdepth!=None:
				assert all(type(s) is not list for s in si)
		# if verdepth!=None:
		# 	self.verdepth = verdepth
		# 	self.complexity = 1+self.obj.complexity
		# 	self.touches = {k for k in self.obj.touches if k<verdepth}
		# 	self.softtouches = {k for k in self.obj.softtouches if k<verdepth}
	def writefile(self,file):
		file.writeChar("G")
		file.writeStrInc(self.si)
		self.obj.writefile(file)

	def detect(self,ranges):
		return self.obj.detect(ranges)


	def look(self,result,lowerbound=False):
		self.obj.look(result,lowerbound=lowerbound)

		for i in range(self.verdepth,self.verdepth+len(self.si)): result.discard(i)

		# for i in result:
		# 	if i>=self.verdepth: result.remove(i)
	def advlook(self,result,pushes,lowerbound=False):
		self.obj.advlook(result,pushes,lowerbound=lowerbound)
		for i in range(self.verdepth+pushes.lenchange,self.verdepth+pushes.lenchange+len(self.si)):
			result.discard(i)
		# if hasattr(pushes,'lookmemo'):
		for i in range(self.verdepth,self.verdepth+len(self.si)):
			pushes.lookmemo.discard(i)

		# for i in result:
		# 	if i>=self.verdepth: result.remove(i)


	def simpush(self,alo):
		short = alo.mem2.get(id(self));
		if short!=None: return short
		res = Lambda(self.si,self.obj.simpush(alo),verdepth=self.verdepth+alo.amt,pos=self)
		alo.mem2[id(self)] = res
		return res



	def hascorrectlinks(self,yooj={}):
		yooj = copy.copy(yooj)
		for x in range(self.verdepth,self.verdepth+len(self.si)): yooj[x]=None
		self.obj.hascorrectlinks(yooj)

	def canbetranslated(self,pushes):
		if alreadycanbetranslated(self,pushes): return
		self.obj.canbetranslated(ScopeDelta([([(x,None) for x in range(self.verdepth,self.verdepth+len(self.si))],)])+pushes)


	def dpush(self,pushes,exob=None,frozen=False,selective=None):
		early = pushes.getmemo(self,exob,frozen)
		if early!=None: return early
		if exob!=None:
			aftburn = self.verdepth+pushes.lenchange
			jsi = self.si[:len(exob.subs)] if len(self.si)>len(exob.subs) else self.si
			nexob = SubsObject(exob.subs[:len(self.si)],verdepth=exob.verdepth) if len(exob.subs)>len(self.si) else exob
			adob = None
			if len(exob.subs)>len(self.si):
				adob = SubsObject(exob.subs[len(self.si):],verdepth=exob.verdepth)#.dpush(ScopeDelta([(aftburn-exob.verdepth,exob.verdepth)]),frozen=True)
			res = self.obj.dpush(pushes+ScopeDelta([(coflattenunravel(jsi,nexob,aftburn),),(-longcount(jsi),aftburn)]),exob=adob,frozen=frozen,selective=selective)
			if len(self.si)>len(exob.subs): res = res.addlambdasphase2(self.si[len(exob.subs):],pos=self)
			if selective==None: pushes.setmemo(self,exob,frozen,res)
			return res
		res = self.obj.dpush(pushes,frozen=frozen,selective=selective).addlambdasphase2(self.si,pos=self)
		if selective==None: pushes.setmemo(self,exob,frozen,res)
		return res

	def isemptyinst(self,si,prep=None):
		lc = striphuman(self.verdepth,self.si)[0]
		prep = lc if prep==None else prep+lc
		return self.obj.isemptyinst(si,prep=prep)

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else other.correction()+rigpush)
		if type(other) is RefTree and other.core!=None: return self.compare(other.unwrapOne(),odsc,thot,extract,lefpush,rigpush)
		if (type(other) is not Lambda or len(self.si)!=len(other.si)) and type(self.obj) is ScopeComplicator:
			return self.obj.decode().addlambdasphase2(self.si).compare(other,odsc,thot,extract,lefpush,rigpush)
		if (type(other) is not Lambda or len(self.si)!=len(other.si)) and type(self.obj) is RefTree and self.obj.core!=None:
			return self.obj.unwrapOne().addlambdasphase2(self.si).compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not Lambda: return False
		if len(self.si)<len(other.si) and conservativeeq(self.si,other.si[:len(self.si)]):
			return Lambda(self.si[len(self.si):],self.obj,verdepth=other.verdepth).compare(other,odsc,thot,extract,lefpush,rigpush)
		return conservativeeq(self.si,other.si) and self.obj.compare(other.obj,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		if len(self.si) == 0: return self.obj.needscarry()
		return True
	
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		if len(self.si) == 0: return self.obj.verify(indesc,carry,reqtype,then)
		if carry==None: raise TypeRequiredError(self,True)
		# if len(self.si)!=carry.args.
		try:
			truncargs,ntype = carry.extractfibration(indesc,self.si,blame=self)
		except InvalidSplit as u:
			raise u.reblame(self,carry,self.si,indesc)
		flatver,converter = truncargs.flatten(ScopeDelta([]),self.si,then=True)
		nindesc = indesc.addflat(flatver)
		return self.obj.verify(nindesc,ntype.dpush(converter)).addlambdasphase2(self.si,pos=self)



	def prepr(self,context,trail):
		if type(self.obj) is ScopeComplicator and not context.printcomplicators:
			return self.obj.decode().addlambdasphase2(self.si).prepr(context,trail)
		if type(self.obj) is RefTree and self.obj.core!=None and context.shouldunwrap(self.obj.name,trail):
			return self.obj.unwrapOne().addlambdasphase2(self.si).prepr(context,trail)
		word = context.newcolors(self.si)
		return pmultilinelist(self.si,context,word)+self.obj.prepr(context.addbits(word),trail)
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		if type(self.obj) is ScopeComplicator and not context.printcomplicators:
			return self.obj.decode().addlambdasphase2(self.si).pmultiline(context,trail,out,indent,prepend,postpend,callback=callback)
		if type(self.obj) is RefTree and self.obj.core!=None and context.shouldunwrap(self.obj.name,trail):
			return self.obj.unwrapOne().addlambdasphase2(self.si).pmultiline(context,trail,out,indent,prepend,postpend,callback=callback)
		word = context.newcolors(self.si)
		self.obj.pmultiline(context.addbits(word),trail,out,indent,prepend+pmultilinelist(self.si,context,word),postpend,callback)
class Strategy(Tobj):

	def innertrim(self,si=None,disgrace=None):#Strategy
		return self.type.innertrim(si=si,disgrace=disgrace).addfibration(self.args)

	def __eq__(self,other):
		return type(other) is Strategy and self.args == other.args and self.type == other.type
	def __hash__(self):
		if self.cachehash != None: return self.cachehash
		self.cachehash = hash((self.args,self.type))
		return self.cachehash


	@initTobj
	def __init__(self,args=None,type=None,verdepth=None,pos=None):
		global encounters
		self.args = DualSubs(pos=pos,verdepth=verdepth) if args == None else args
		self.type = type
		self.verdepth = verdepth
		self.cachehash = None
		transferlines(self,pos)
	def isemptytype(self):
		return self.type.isemptytype()

	def getbecsafety(self):
		if hasattr(self,'becsafety'): return self.becsafety
		return len(self.args)

	def writefile(self,file):
		file.writeChar("E")
		self.args.writefile(file,shutup=True)
		self.type.writefile(file)


	def detect(self,ranges):
		if self.args.detect(ranges,worrynot=True) or self.type.detect(ranges): return True
		if hasattr(ranges,'precal'): ranges.precal = [a for a in ranges.precal if a<self.verdepth]
		return False
		


	def look(self,result,lowerbound=False):
		self.args.look(result,worrynot=True,lowerbound=lowerbound)
		self.type.look(result,lowerbound=lowerbound)
		for i in range(self.verdepth,self.verdepth+longcount(self.args)): result.discard(i)

		# for i in result:
		# 	if i>=self.verdepth: result.remove(i)
	def advlook(self,result,pushes,lowerbound=False):
		self.args.advlook(result,pushes,worrynot=True,lowerbound=lowerbound)
		self.type.advlook(result,pushes,lowerbound=lowerbound)
		for i in range(self.verdepth+pushes.lenchange,self.verdepth+pushes.lenchange+longcount(self.args)):
			result.discard(i)
		# if hasattr(pushes,'lookmemo'):
		for i in range(self.verdepth,self.verdepth+longcount(self.args)):
			pushes.lookmemo.discard(i)
		# 	if self.verdepth+pushes.lenchange+i in result:



		# for i in result:
		# 	if i>=self.verdepth: result.remove(i)


	def simpush(self,alo):
		short = alo.mem2.get(id(self));
		if short!=None: return short
		res = Strategy(self.args.simpush(alo),self.type.simpush(alo),verdepth=self.verdepth+alo.amt,pos=self)
		alo.mem2[id(self)] = res
		return res



	def hascorrectlinks(self,yooj={}):
		yooj = copy.copy(yooj)
		self.args.hascorrectlinks(yooj,isolate=False)
		self.type.hascorrectlinks(yooj)

	def canbetranslated(self,pushes):
		if alreadycanbetranslated(self,pushes): return
		self.args.canbetranslated(pushes)
		assist = []
		sof = self.verdepth
		for r in range(len(self.args.rows)):
			vv = longcount(self.args.rows[r].name)
			if self.args.rows[r].obj==None:
				for j in range(sof,sof+vv):
					assist.append((j,None))
			sof+=vv
		try:
			self.type.canbetranslated(ScopeDelta([(assist,)])+pushes)
		except Exception as u:
			print("EXCEPTINO @")
			print("\t",ScopeDelta([(assist,)])+pushes)
			print("\t",self)
			print("\t",self.verdepth)
			raise u



	# canbetranslated passes, then dpush happens, then canbetranslated does not pass
	# this is a contradiction because no sub should be coming in above the verification depth.



	def dpush(self,pushes,exob=None,frozen=False,selective=None):
		early = pushes.getmemo(self,exob,False)
		if early!=None: return early

		# disgrace = ScopeDelta()
		newargs = self.args.dpush(pushes,worrynot=True)
		newtype = self.type.dpush(pushes)
		if hasattr(pushes,'delaymemo'):

			for k in range(self.verdepth+pushes.lenchange,self.verdepth+pushes.lenchange+longcount(self.args)):
				pushes.delaymemo.pop(k,None)
			# pushes.delaymemo = {k:v for (k,v) in pushes.delaymemo.items() if k<self.verdepth+pushes.lenchange}
		res = newtype.addfibration(newargs,pos=self)
		pushes.setmemo(self,exob,False,res)
		return res

	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else other.correction()+rigpush)
		if type(other) is RefTree:
			att = other.mangle_FE()
			if att!=None: return self.compare(att,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not Strategy: return False


		if len(other.args)<len(self.args) and type(other.type) is ScopeComplicator:
			return self.compare(other.type.decode().addfibration(other.args),odsc,thot,extract,lefpush,rigpush)
		if len(other.args)<len(self.args) and type(other.type) is RefTree:
			att = other.type.mangle_FE()
			if att!=None: return self.compare(att.addfibration(other.args),odsc,thot,extract,lefpush,rigpush)



		if lefpush==None: lefpush = ScopeDelta()
		if rigpush==None: rigpush = ScopeDelta()
		lefpush = lefpush.isolate()
		rigpush = rigpush.isolate()
		adv = []
		st = len(lefpush.pushes)
		if not self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush,keepr=True,advanced=adv): return False
		if len(adv):
			mdsc = self.verdepth+lefpush.lenchange+longcount(self.args)-rigpush.lenchange#longcount([k.name for k in adv])
			other = Strategy(DualSubs(adv,verdepth=mdsc),other.type,verdepth=mdsc)
		else:
			other = other.type
		return self.type.compare(other,odsc,thot,extract,lefpush,rigpush)
	def addfibration(self,args,pos=None,alts=None):
		return Strategy(args+self.args,self.type,pos=self,verdepth=self.verdepth-longcount(args))
	def semavail(self,mog=False):
		return self.type.semavail(mog)
	def emptyinst(self,limit,mog,prep=None):
		if type(mog) is not list: return Tobj.emptyinst(self,limit,mog,prep)
		trimargs = self.args.trimallnonessential()
		sc = longcount(trimargs)
		if prep == None: prep = SubsObject([],verdepth=limit)
		prep = prep.simpush(SimpleDelta(limit+sc-prep.verdepth,prep.verdepth)).subs if prep != None else []
		art = trimargs.emptyinst(limit)
		tat = self.type.emptyinst(limit+sc,mog,SubsObject(prep+art.subs,verdepth=limit+sc))
		return correctLambda([k.name for k in trimargs.rows],tat,ScopeDelta(),verdepth=limit)
	def trimallnonessential(self,si=None):
		disgrace = ([],[])
		nargs = self.args.trimallnonessential(si,disgrace)
		# ntype = complicate(self.type.dpush(ScopeDelta([(c[1],c[0],left,0) for c in disgrace[0]])),disgrace[1],names=disgrace[2])
		ntype = compassionate_reshift(self.type,disgrace[0],disgrace[1])
		# if len(disgrace[0]): ntype = complicate(ntype.dpush(ScopeDelta([(c[1],c[0],ntype.verdepth,0) for c in disgrace[0]])),disgrace[1],names=disgrace[2])
		return Strategy(nargs,ntype,verdepth=self.verdepth,pos=self)
	@lazyflatten
	def flatten(self,delta,mog,assistmog,prep=None,obj=None,fillout=None,then=False):
		if obj != None:
			obj = DelayedComplication(obj.ob.dpush(obj.srows,exob=self.args.emptyinst(obj.ob.verdepth+ob.srows.lenchange-longcount(self.args))))
		arp = self.args.dpush(delta)
		if prep == None:
			njprep = arp
		else:
			lindsk = self.verdepth+delta.lenchange
			calmdown = prep.simpush(SimpleDelta(lindsk-longcount(prep)-prep.verdepth,prep.verdepth))
			njprep = DualSubs(calmdown.rows+arp.rows,verdepth=calmdown.verdepth)
		return self.type.flatten(delta,mog,assistmog,njprep,obj,fillout=fillout,then=then)
	def needscarry(self):
		if len(self.args) == 0: return self.type.needscarry()
		return False
	

	def reverse_mangle_FE(self):
		component = self.trimallnonessential()
		if type(component.type) is not RefTree: return None
		comptype = component.type.unwrap()
		if type(comptype) is not RefTree or comptype.src!=None or comptype.name!=1: return None
		return RefTree(1,SubsObject([
			SubRow(None,comptype.args.subs[0].obj.addfibration(component.args)),
			SubRow(None,comptype.args.subs[1].obj.addlambdasphase2([j.name for j in component.args.rows])),
			SubRow(None,comptype.args.subs[2].obj.addlambdasphase2([j.name for j in component.args.rows]))
		],verdepth=self.verdepth),verdepth=self.verdepth)

	def verify(self,indesc,carry=None,reqtype=False,then=False):
		verargs,thendesc = self.args.verify(indesc,then=True)
		if len(verargs) == 0:
			# thendesc = thendesc.posterase(len(indesc))
			vertype = self.type.verify(thendesc,None if carry==None else carry.simpush(SimpleDelta(longcount(verargs),len(indesc))),reqtype=reqtype,then=then)
			# return vertype.dpush( ScopeDelta([(-longcount(verargs),len(indesc))]))
			rip = verargs.rip()
			names = longlist(verargs)
			if reqtype:
				verobj,vertype = vertype
				verobj = entrycomplicate(verobj,rip,pos=self,names=names)
				vertype = entrycomplicate(vertype,rip,pos=self,names=names)
				# verobj.legaltracking=False
				return verobj,vertype

			for r in rip: assert type(r) is DelayedComplication
			mou = entrycomplicate(vertype,rip,pos=self,names=names)
			# mou.legaltracking=False
			return mou

		assertstatequal(indesc,self,carry,u_type(len(indesc)))
		vertype = self.type.verify(thendesc,u_type(len(thendesc)))
		outp = vertype.addfibration(verargs)

		return (outp,u_type(len(indesc))) if reqtype else outp
	def prepr(self,context,trail):
		if type(self.type) is ScopeComplicator and not context.printcomplicators:
			return self.type.decode().addfibration(self.args).prepr(context,trail)
		if type(self.type) is RefTree and self.type.core!=None and context.shouldunwrap(self.type.name,trail+[len(self.args.rows)]):
			return self.type.unwrapOne().addfibration(self.args).prepr(context,trail)

		if context.shouldtrim(trail) and any(row.obj!=None for row in self.args.rows) and self.verdepth!=None:
			return self.trimallnonessential().prepr(context,trail)
		res = []
		for k in self.args.rows:
			word = context.newcolors(k.name)
			res.append(k.prepr(context,trail+[k],word=word))
			context = context.addbits(word)
		return context.red("[")+",".join(res)+context.red("]")+(self.type.prepr(context,trail+[len(res)]) if self.type!=None else "None")
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		if type(self.type) is ScopeComplicator and not context.printcomplicators:
			return self.type.decode().addfibration(self.args).pmultiline(context,trail,out,indent,prepend,postpend,callback=callback)
		if type(self.type) is RefTree and self.type.core!=None and context.shouldunwrap(self.type.name,trail+[len(self.args.rows)]):
			return self.type.unwrapOne().addfibration(self.args).pmultiline(context,trail,out,indent,prepend,postpend,callback=callback)

		if context.shouldtrim(trail) and any(row.obj!=None for row in self.args.rows) and self.verdepth!=None:
			return self.trimallnonessential().pmultiline(context,trail,out,indent,prepend,postpend,callback)
		def calls(context,out,prepend):
			self.type.pmultiline(context,trail+[len(self.args.rows)],out,indent,prepend,postpend,callback=callback)
		pmultilinecsv(context,trail,out,indent,self.args.rows,prepend+context.red("["),context.red("]"),lamadapt=lambda n,x:x.name,callback=calls,delim=context.red(","))
def u_type(verdepth):
	return RefTree(verdepth=verdepth)
class RefTree(Tobj):

	def innertrim(self,si=None,disgrace=None):#RefTree
		ja = self.mangle_UE()
		if ja==None: raise InvalidSplit()
		return ja.innertrim(si=si,disgrace=disgrace)


	def __eq__(self,other):
		return type(other) is RefTree and self.name == other.name and self.args == other.args and self.src == other.src and self.core == other.core
	def __hash__(self):
		if self.cachehash != None: return self.cachehash
		self.cachehash = hash(tuple([self.src,self.name,self.core]+([] if self.args==None else [a.obj for a in self.args.subs])))
		return self.cachehash
	@initTobj
	def __init__(self,name=None,args=None,src=None,verdepth=None,pos=None,core=None):
		self.name = 0 if name == None else name
		self.args = args
		self.src = src
		self.core = core
		self.verdepth = verdepth
		self.cachehash = None

		# if self.args!=None: assert len(self.args.subs)
		transferlines(self,pos)


		if self.src!=None and verdepth!=None:
			assert type(self.src.isSubOb()) is not bool
		def _dbgTest():
			if self.args!=None: assert not self.args.isfrozen()
			# if self.core!=None and self.name==5:
			# 	assert not self.core.core.dpush(self.core.rows).detect(ScopeDelta([(self.name-self.verdepth,self.name)]))
			if self.args!=None: assert len(self.args.subs)>0
			assert type(self.name) is int or type(self.name) is str
			if self.src==None and self.verdepth!=None and self.name!=0:
				assert self.name<self.verdepth
			assert self.args==None or type(self.args) is SubsObject
			if self.core!=None:
				jaha = self.core.isSubOb()
				if type(jaha) is int: assert jaha<self.name
				if type(jaha) is Inspection: 
					if not jaha.root<self.name:
						print("-="*20)
						print("\t",self)
						print("\t",self.core)
						# assert False
						try:
							print("\t",self.unwrap())
						except Exception as u:
							print("\tfailed to print")
						assert False
			if self.src!=None:
				if self.verdepth!=None:
					assert type(self.src) is RefTree

					if type(self.src.isSubOb()) is tuple:
						assert False
	def semavail(self,mog=False):
		return self.unwrap().semavail(mog)
	def writefile(self,file):
		if self.args!=None:
			if self.src==None:
				file.writeChar("H")
				file.writeNum(self.name)
				self.args.writefile(file,shutup=True)
			else:
				file.writeChar("I")
				file.writeNum(self.name)
				self.args.writefile(file,shutup=True)
				self.src.writefile(file)
		else:
			if self.src==None:
				file.writeChar("A")
				file.writeNum(self.name)
			else:
				file.writeChar("B")
				file.writeNum(self.name)
				self.src.writefile(file)
	

	def unwrc(self):
		if self.verdepth==self.core.verdepth: return ScopeDelta()
		return ScopeDelta([(self.verdepth-self.core.verdepth,min(self.core.verdepth,self.verdepth))])#you will need to fix this<><><><><> so that the min thing is applied everywhere
	# def unwrs(self):


	def unwrap(self):
		if self.core==None: return self
		ja = self.unwrapOne()
		if type(ja) is ScopeComplicator: ja = ja.decode()
		if type(ja) is RefTree: ja = ja.unwrap()
		return ja
	def unwrapOne(self,selective=None):
		def _dbgExit(outp):
			assert outp.verdepth==self.verdepth
		if self.args==None and self.core.verdepth==self.verdepth: return self.core
		if selective!=None: return self.core.dpush(self.unwrc(),exob=self.args,frozen=True,selective=selective)
		# if self.args==None: return self.core.simpush(SimpleDelta(self.verdepth-self.core.verdepth,self.core.verdepth))
		return self.core.dpush(self.unwrc(),exob=self.args)

		# what about memoing this?

		# 	if self.core.rows.isempty():
		# 		return self.core.core
		# 	# self.core.rows.tampdown()
		# 	# if len(self.core.rows.pushes)==1 and len(self.core.rows.pushes[0])==2 and self.core.rows.pushes[0][0]>=0:
		# 	# 	am = self.core.core.simpush(SimpleDelta(self.core.rows.pushes[0][0],self.core.rows.pushes[0][1]))
		# 	# 	self.core.core = am
		# 	# 	self.core.rows = ScopeDelta()
		# 	# 	return am
		# 	am = self.core.core.dpush(self.core.rows)
		# 	self.core.core = am
		# 	self.core.rows = ScopeDelta()
		# 	return am
		# guac = self.core.memo.get(self.args)
		# if guac==None:
		# 	fo = self.core.core.dpush(self.core.rows,exob=self.args)
		# 	self.core.memo[self.args] = fo
		# 	return fo
		# return guac
	def detect(self,ranges):
		if self.core!=None:
			if self.args!=None and self.args.detect(ranges): return True#return self.unwrapOne().detect(ranges)#<><><><><><>a component of arg might be unusued....
			if hasattr(ranges,'precal') and self.name in ranges.precal: return False
			if ranges.islowerbound(self.name): return False
			if self.core.detect(self.unwrc() + ranges): return self.unwrapOne().detect(ranges)#<><><><><> a specific component of a sub could be unused.
			if not hasattr(ranges,'precal'): ranges.precal = []
			ranges.precal.append(self.name)
			return False
		if self.src==None:
			if not ranges.canTranslate(self.name,inlen=self.verdepth): return True
		else:
			A = firstSubObPush(self.src.isSubOb(),ranges,self.verdepth)
			if A!=None: return self.dpush(A[0]).detect(A[1])
			if self.src.detect(ranges): return True
		return self.args!=None and self.args.detect(ranges)
	def look(self,result,lowerbound=False):
		if self.args!=None:
			for sub in self.args.subs: sub.obj.look(result,lowerbound=lowerbound)
		if self.src==None: result.add(self.name)
		elif (not lowerbound) or type(self.src) is RefTree and self.src.core==None: self.src.look(result)
	def advlook(self,result,pushes,lowerbound=False):
		if self.args!=None:
			for sub in self.args.subs: sub.obj.advlook(result,pushes,lowerbound=lowerbound)
		if self.src==None:
			# if not hasattr(pushes,'lookmemo'): pushes.lookmemo=set()
			if self.name not in pushes.lookmemo:
				try:
					mow = pushes.translate(self.name,inlen=self.verdepth)
				except DpushError:
					if self.core!=None:
						madra = self.unwrc()+pushes
						madra.lookmemo = set()
						self.core.advlook(result,madra,lowerbound=lowerbound)
				else:
					if type(mow) is tuple:
						if mow[2] != None:
							result.add(mow[2])
						else:
							mow[1].lookmemo = set()
							mow[0].advlook(result,mow[1],lowerbound=lowerbound)
					else:
						result.add(mow)
				pushes.lookmemo.add(self.name)
		elif not lowerbound:
			self.src.advlook(result,pushes)
		elif type(self.src) is RefTree and self.src.core==None and self.src.src==None:
			# if self.src.name not in pushes.lookmemo:
			mow = pushes.translate(self.src.name,inlen=self.verdepth)
			if type(mow) is tuple: return
			else: result.add(mow)
			pushes.lookmemo.add(self.src.name)
			if self.src.args!=None:
				for sub in self.src.args.subs: sub.obj.advlook(result,pushes,lowerbound=lowerbound)
	def simpush(self,alo):
		short = alo.mem2.get(id(self));
		if short!=None: return short
		# skip = None

		dnet = self.name if self.name<alo.lim else self.name+alo.amt
		core = self.core if self.name<alo.lim else None if self.core==None else self.core.simpush(alo)
		# if self.core!=None:
		# 	skip = alo.mem1.get(id(self.core))
		# 	if skip == None:
		# 		skip = self.core.dpush_ds(ScopeDelta([(alo.amt,alo.lim)]),dnet)
		# 		alo.mem1[id(self.core)] = skip
			# print("-=-=-")
			# print(alo.amt)
			# print(alo.lim)
			# print(self.name)
			# print(skip.isSubOb)
			# print(self.name if self.name<alo.lim else self.name+alo.amt)
		def _dbgTest():
			assert self.name<alo.lim or self.name+alo.amt>=alo.lim
		res = RefTree(dnet,None if self.args==None else self.args.simpush(alo),None if self.src==None else self.src.simpush(alo),verdepth=self.verdepth+alo.amt,pos=self,core=core)
		alo.mem2[id(self)] = res
		return res


	def hascorrectlinks(self,yooj={}):
		if self.args!=None: self.args.hascorrectlinks(yooj)
		if self.src!=None: self.src.hascorrectlinks(yooj)
		else:
			if self.name in yooj:
				ma = yooj.get(self.name)
				# if self.name==77:
					# print("i'm 77; expected is ",ma,"and my core is",None if self.core==None else self.core.isSubOb())
				if not ( ((ma==None) and (self.core==None)) or ma==self.core.isSubOb()  ):
					print("expected issubob: ",ma,"but got",self.core.isSubOb()," on token named ",self.name)
					print("total references: ",yooj)
					assert False
			if self.core!=None: self.core.hascorrectlinks({k:v for k,v in yooj.items() if k<self.core.verdepth})


	def canbetranslated(self,pushes):
		if alreadycanbetranslated(self,pushes): return
		# if self.core!=None:
		# 	try:
		# 		self.core.canbetranslated(self.unwrc()+pushes)
		# 	except Exception as u:
		# 		print("CANBETRANSLATED ERROR WITHIN DELAY CORE: ",self.name)
		# 		print("\t",self.core)
		# 		print("\t",self.unwrc())
		# 		print("\t",pushes)
		# 		raise u
			# (self.core.rows+pushes).objconforms(self.core.core)
		if self.args!=None: self.args.canbetranslated(pushes)
		if self.src!=None: self.src.canbetranslated(pushes)

	def dpush(self,pushes,exob=None,frozen=False,selective=None):
		# def _d
		early = pushes.getmemo(self,exob,frozen)
		if early!=None: return early
		gy = self.name
		pushdepth = self.verdepth+pushes.lenchange
		decargs = SubsObject([],verdepth=self.verdepth) if self.args==None else ( self.args if pushes.isempty() else self.args.dpush(pushes,frozen=True) )
		if exob != None and exob.verdepth<pushdepth: exob = exob.simpush(SimpleDelta(pushdepth-exob.verdepth,exob.verdepth))
		if exob != None: decargs = SubsObject(decargs.subs+exob.subs,verdepth=pushdepth)
		decargs = decargs if len(decargs.subs) else None
		if self.src!=None:
			outp = self.src.dpush(pushes,frozen=True)
			outp = outp.reference(self.name,decargs)
			if outp==None: raise DpushError
			if not frozen and outp.isfrozen(): raise DpushError()
			pushes.setmemo(self,exob,frozen,outp)
			return outp
		if self.name!=0:
			if self.core!=None and not pushes.canTranslate(self.name,ignoresubs=True):
				res = self.core.dpush(self.unwrc()+pushes,exob=decargs,frozen=frozen,selective=selective)
				if selective==None: pushes.setmemo(self,exob,frozen,res)
				return res
			gy = pushes.translate(self.name,ignoresubs=self.core!=None,inlen=self.verdepth)
		if type(gy) is int:
			if decargs!=None and decargs.isfrozen():
				if self.core==None: raise DpushError()
				res = self.core.dpush(self.unwrc()+pushes,exob=decargs,frozen=frozen)
				pushes.setmemo(self,exob,frozen,res)
				return res

			# def _dbgTest():
			# 	pushes.conforms(self.verdepth)
			# 	if self.core!=None:
			# 		assert self.unwrc().lenchange+self.core.verdepth == self.verdepth
			# 		assert (self.unwrc()+pushes).lenchange == self.unwrc().lenchange + pushes.lenchange
			# 		self.unwrc().conforms(self.core.verdepth)
			# 		pushes.conforms(self.verdepth)
			# 		(self.unwrc()+pushes).conforms(self.core.verdepth)
			# try:
				# yass = 
			whomd = None
			if self.core!=None:
				if hasattr(pushes,'delaymemo'):
					whomd = pushes.delaymemo.get(gy)
				else: pushes.delaymemo = {}
				if whomd==None:
					whomd = self.core if pushes.islowerboundRev(gy) else self.core.dpush(self.unwrc()+pushes)
					pushes.delaymemo[gy] = whomd

			res = RefTree(gy,decargs,None,pos=self,verdepth=pushdepth,core=whomd)#None if self.core==None else pushes.memoizeGet(self.unwrc()+pushes,gy,self.core))
			# except Exception as u:
			# 	print("tempresult:",gy,yass)
			# 	print(self.unwrc()+pushes)
			# 	print(pushes,self.name,gy,(self.unwrc()+pushes).islowerboundRev(gy))
			# 	raise u
			pushes.setmemo(self,exob,False,res)
			return res
		elif len(gy)==3:
			pard = self.dpush(gy[1])
			for j in range(len(gy[0])):
				if pard.compare(gy[0][j]):
					vdep = self.verdepth+pushes.lenchange-gy[2].lenchange
					ae = RefTree(vdep-len(gy[0])+j,verdepth=vdep)
					if exob!=None or not gy[2].isempty(): ae = ae.dpush(gy[2],exob=exob)
					pushes.setmemo(self,exob,False,ae)
					return ae
			raise DpushError
		else:
			if gy[0]==None: raise DpushError()
			froze = gy[0].isfrozen()
			if froze and not frozen: raise DpushError()
			# sems = ScopeDelta([(self.verdepth+gy[3]-gy[0].verdepth,gy[0].verdepth)])+gy[1]
			# sems.tampdown()
			if froze or gy[2]==None or decargs!=None and decargs.isfrozen():
				# if decargs==None and not frozen and len(sems.pushes)==1 and len(sems.pushes[0])==2 and sems.pushes[0][0]>=0:
				# 	res = gy[0].simpush(SimpleDelta(sems.pushes[0][0],sems.pushes[0][1]))
				# else:
				res = gy[0].dpush(gy[1],exob=decargs,frozen=frozen)
				pushes.setmemo(self,exob,frozen,res)
				return res
			else:
				assert self.core == None
				whomd = None
				if hasattr(pushes,'delaymemo'):
					whomd = pushes.delaymemo.get(gy[2])
				else: pushes.delaymemo = {}
				if whomd==None:
					whomd = gy[0] if gy[1].islowerboundRev(gy[2]) else gy[0].dpush(gy[1])
					pushes.delaymemo[gy[2]] = whomd

				# make sure the memo gets copied to gy[0]<><><><>

				res = RefTree(
					gy[2],
					decargs,
					pos=self,
					verdepth=pushdepth,
					core = whomd#pushes.memoizeGet(gy[1],gy[2],gy[0])
				)
				pushes.setmemo(self,exob,False,res)
				return res

	def isemptyinst(self,si,prep=None):
		if type(si) is list: return False
		if self.name!=si: return False
		return (prep==None)==(self.args==None) and (self.args==None or self.args.isemptyinst(prep))
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		# dbgstarter = copy.copy(rigpush)

		if type(other) is ScopeComplicator: return self.compare(other.core,odsc,thot,extract,lefpush,other.correction() if rigpush==None else other.correction()+rigpush)
		if self.src != None:
			if type(other) is not RefTree: return False
			if other.src==None: other = other.unwrap()
			if type(other) is not RefTree: return False
			if other.src==None or self.name!=other.name: return False
			return self.src.compare(other.src,odsc,thot,extract,lefpush,rigpush) and (self.args==None) == (other.args==None) and (self.args==None or self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush))
		pTest = self.isSubOb()
		if thot != None and type(pTest) is int and (lefpush==None or lefpush.canTranslate(pTest)):
			pTest = pTest if lefpush==None else lefpush.translate(pTest)
			for k in thot:
				if k[0] == pTest:
					subself = self.unwrap() if lefpush==None else self.dpush(lefpush).unwrap()
					for j in extract:
						if j[0] == k[1] and j[2] == False:
							return True
					repls = []
					valid = True
					dsc = subself.verdepth
					if subself.args!=None:
						for g1 in range(len(subself.args.subs)):
							if type(subself.args.subs[g1].obj) is not RefTree or subself.args.subs[g1].obj.name<odsc:
								valid = False
								break
							for g2 in range(g1):
								if subself.args.subs[g1].obj.compare(subself.args.subs[g2].obj):
									valid = False
									break
							if not valid: break
							repls.append(subself.args.subs[g1].obj)
					if not valid: break
					def _dbgTest():
						other.setSafety(dsc-(0 if rigpush==None else rigpush.lenchange))

					# if len(repls):
					try:
						if odsc==dsc:
							gr = other if rigpush==None else other.dpush(rigpush)
						else:
							gr = other.dpush((ScopeDelta() if rigpush==None else rigpush) + (ScopeDelta([(odsc-dsc,odsc,repls)]) if len(repls) else ScopeDelta([(odsc-dsc,odsc)])))
					except  DpushError:
						print("there was a dpusherror preventing: ",self)
						# print("\t",)
						# print("\t",other.prepr(FormatterObject(None,fullrepresent=True)))
						# print("\t",((ScopeDelta() if rigpush==None else rigpush) + (ScopeDelta([(odsc-dsc,odsc,repls)]) if len(repls) else ScopeDelta([(odsc-dsc,odsc)]))))
						continue
					# else:
					# 	if other.detect((ScopeDelta() if rigpush==None else rigpush) + ScopeDelta([(odsc-dsc,odsc)])):
					# 		print("there was a dpusherror preventing: ",self)
					# 		print("\t",other)
					# 		continue
					# 	else:
					# 		gr = other.dpush((ScopeDelta() if rigpush==None else rigpush) + ScopeDelta([(odsc-dsc,odsc)]))

					def _dbgTest():
						gr.setSafety(odsc+len(repls))
					mod = gr.addlambdasphase2(["_"]*len(repls))
					def _dbgTest():
						mod.setSafety(odsc)
					for j in extract:
						if j[0] == k[1]:
							return j[1].compare(mod)
					extract.append((k[1],mod,True))
					return True
		# oTest = other.isSubOb()
		# if pTest!=oTest: return False
		if self.core==None and type(other) is RefTree and other.core!=None:

			return self.compare(other.unwrap(),odsc,thot,extract,lefpush,rigpush)

			# other=other.unwrap()
			# while type(other) is ScopeComplicator:
			# 	rigpush = other.correction() if rigpush==None else other.correction()+rigpush
			# 	other = other.core
		if self.core!=None and (type(other) is not RefTree or other.core==None):
			return self.unwrap().compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is Strategy: 
			att = self.mangle_FE()
			if att==None:
				natt = other.reverse_mangle_FE()
				if natt==None: return False
				return self.compare(natt,odsc,thot,extract,lefpush,rigpush)
			
			return att.compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is DualSubs:
			att = self.mangle_UE()
			if att==None: return False
			return att.compare(other,odsc,thot,extract,lefpush,rigpush)
		if type(other) is not RefTree or other.src!=None:
			# assert False
			return False
		if self.core==None and other.core==None:
			return (self.name if lefpush==None else lefpush.translate(self.name))==(other.name if rigpush==None else rigpush.translate(other.name)) and (self.args==None)==(other.args==None) and (self.args==None or self.args.compare(other.args,odsc,thot,extract,lefpush,rigpush))
		aH=self
		bH=other
		# def _dbgTest():
		# 	if lefpush!=None: assert not aH.detect(lefpush)
		# 	if rigpush!=None: assert not bH.detect(rigpush)
		a = []
		b = []
		while True:
			# def _dbgTest():
			# 	if lefpush!=None: assert not aH.detect(lefpush)
			# 	if rigpush!=None: assert not bH.detect(rigpush)
			if type(aH) is RefTree and aH.core!=None:
				if lefpush==None or lefpush.canTranslate(aH.name):
					aname = aH.name if lefpush==None else lefpush.translate(aH.name)
					for g,bname in b:
						if aname==bname:
							if extract!=None: st = len(extract)
							if (aH.args==None)==(g.args==None) and (aH.args==None or aH.args.compare(g.args,odsc,thot,extract,lefpush,rigpush)): return True
							elif extract!=None:
								while st<len(extract): del extract[st]
					a.append((aH,aname))
					aH = aH.unwrapOne().decode()
				else:
					aH = aH.unwrapOne().decode()
			# def _dbgTest():
			# 	if lefpush!=None: assert not aH.detect(lefpush)
			# 	if rigpush!=None: assert not bH.detect(rigpush)

			# dbgobh = bH

			if type(bH) is RefTree and bH.core!=None:
				if rigpush==None or rigpush.canTranslate(bH.name):
					bname = bH.name if rigpush==None else rigpush.translate(bH.name)
					for g,aname in a:
						if aname==bname:
							if extract!=None: st = len(extract)
							if (g.args==None)==(bH.args==None) and (g.args==None or g.args.compare(bH.args,odsc,thot,extract,lefpush,rigpush)): return True
							elif extract!=None:
								while st<len(extract): del extract[st]
					b.append((bH,bname))
					bH = bH.unwrapOne().decode()
				else:
					bH = bH.unwrapOne().decode()

			if (type(aH) is not RefTree or aH.core==None) and (type(bH) is not RefTree or bH.core==None):
				return aH.compare(bH,odsc,thot,extract,lefpush,rigpush)
	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		assert not then
		p1 = [] if self.args==None else self.args.phase1(indesc)
		errorcontext = []
		if self.src == None:
			tra = indesc.symextract(self.name,p1,carry=carry,reqtype=reqtype,pos=self,errorcontext=errorcontext)
			if tra != None: return tra
			if len(errorcontext)==0:
				raise LanguageError(self,"Symbol not defined for these arguments: "+self.name).callingcontext(errorcontext,-1)
			raise LanguageError(self,"Symbol not defined in this context: "+self.name).callingcontext(errorcontext,-1)
		else:
			if self.src.needscarry(): raise LanguageError(self,"Need to be able to generate type for property access...")
			orig = self.src.verify(indesc,reqtype=True)
			anguish = orig[1].unwrflatten(obj=DelayedComplication(orig[0]))

			# examtype = examtype.mangle_UE() if type(examtype) is RefTree else examtype
			if anguish!=None:

				# anguish = examtype.flatten(ScopeDelta([]),obj=DelayedComplication(orig[0]))
				tra = indesc.invisadd(anguish).preerase(len(anguish)).symextract(self.name,p1,carry=carry,reqtype=reqtype,limiter=len(indesc.flat),pos=self,errorcontext=errorcontext)
				if tra != None: return tra

			possib = orig[0].decode()
			while type(possib) is RefTree:
				if possib.src == None:

					retrievalname = indesc.flat[(-indesc.postpushes).translate(possib.name)].name

					possibar = [] if possib.args==None else possib.args.phase1_gentle()
					tra = indesc.symextract(retrievalname+"."+self.name,possibar+p1,reqtype=reqtype,carry=carry,pos=self,cosafety=len(possibar),errorcontext=errorcontext)
					if tra != None: return tra
				if possib.core==None: break
				possib = possib.unwrapOne().decode()

			tra = indesc.symextract("."+self.name,[(None,orig)]+p1,reqtype=reqtype,carry=carry,pos=self,errorcontext=errorcontext)
			if tra != None: return tra
			raise LanguageError(self,"Symbol not defined for these arguments as a property access, macro, or operator overload: "+self.name).callingcontext(errorcontext,-1)
	def prepr(self,context,trail):
		if self.core!=None and context.shouldunwrap(self.name,trail):# or context.context[self.name]==None
			# print("unwrapping:")
			# print("\t",self.core.rows)
			# print("\t",self.core.core)
			return self.unwrapOne().prepr(context,trail+[2 if self.args==None else len(self.args.subs)+2])
		# if self.core!=None: return self.unwrap().prepr(context)
		res = str(context.getname(self.name)) if self.src==None else str(self.name)
		if self.core!=None: res = context.makeclickable(res,trail)
		if self.src != None:
			res = self.src.prepr(context,trail+[0 if self.args==None else len(self.args.subs)])+"."+res
		if self.args!=None: res = res+"("+",".join([self.args.subs[k].prepr(context,trail+[k]) for k in range(len(self.args.subs))])+")"
		return res
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		if len(out)>400: raise OutputTooLong()
		if self.core!=None and context.shouldunwrap(self.name,trail):# or context.context[self.name]==None
			return self.unwrapOne().pmultiline(context,trail+[2 if self.args==None else len(self.args.subs)+2],out,indent,prepend,postpend,callback=callback)
		# if self.core!=None: return self.unwrap().pmultiline(context,out,indent,prepend,postpend,callback=callback)
		def calls(context_,out,prepend):
			res = str(context.getname(self.name)) if self.src==None else str(self.name)
			if self.core!=None: res = context.makeclickable(res,trail)
			if self.args == None:
				if callback == None:
					out.append("\t"*indent+prepend+res+postpend)
				else:
					callback(context,out,prepend+res+postpend)
			else:
				pmultilinecsv(context,trail,out,indent,self.args.subs,prepend+res+"(",")"+postpend,callback=callback)
		if self.src == None: calls(context,out,prepend)
		else:
			self.src.pmultiline(context,trail+[0 if self.args==None else len(self.args.subs)],out,indent,prepend,".",callback=calls)
	def mangle_FE(self):
		component = self.unwrap().decode()
		if type(component) is not RefTree: return component
		if component.name==1 and component.src==None:
			jab = component.args.subs[0].obj.decode()
			if type(jab) is RefTree: jab = jab.mangle_FE()
			if type(jab) is Strategy:
				reduc = jab.trimallnonessential()
				despar = ScopeDelta([(reduc.type.verdepth-self.verdepth,self.verdepth)])
				newparams = reduc.args.emptyinst(self.verdepth)
				return Strategy(reduc.args,RefTree(1,SubsObject([
					SubRow(None,reduc.type),
					SubRow(None,component.args.subs[1].obj.dpush(despar,exob = newparams)),
					SubRow(None,component.args.subs[2].obj.dpush(despar,exob = newparams))
				],verdepth=reduc.type.verdepth),verdepth=reduc.type.verdepth),verdepth=self.verdepth)
		if self.core!=None: return component
		return None
	def mangle_UE(self):
		delta = ScopeDelta([])
		component = self.unwrap().decode()
		if type(component) is not RefTree: return component
		if component.name==1 and component.src==None:
			jab = component.args.subs[0].obj.decode()
			if type(jab) is RefTree: jab = jab.mangle_UE()
			if type(jab) is DualSubs:
				trimmed = jab.trimallnonessential()
				substuff = [(component.args.subs[1].obj.reference(s),component.args.subs[2].obj.reference(s)) for s in range(len(trimmed.rows))]
				inhuman = striphuman(self.verdepth,[a.name for a in trimmed])[0]
				outs = []
				alc = self.verdepth
				sofrefs = []
				for a in range(len(trimmed.rows)):
					toalc = ScopeDelta([(alc-self.verdepth,self.verdepth)])
					tsimp = SimpleDelta(alc-self.verdepth,self.verdepth)
					refs = [a]
					lc = self.verdepth
					for b in range(a):
						tlc = longcount(trimmed.rows[b].name)
						if trimmed.rows[a].type.detect(ScopeDelta([(-tlc,lc)])): refs = sorted(refs+[k for k in sofrefs[b] if k not in refs])
						lc+=tlc
					sofrefs.append(refs)
					nurows = []
					hedge = []
					lc = self.verdepth
					for b in range(a+1):
						tlc = longcount(trimmed.rows[b].name)
						if b in refs:
							nurows.append(trimmed.rows[b].type.dpush(ScopeDelta(hedge)+toalc))
							lc+=tlc
						else: hedge.append([(-tlc,lc)])
					thad = [trimmed.rows[b].name for b in refs[:-1]]
					if len(refs) == 1:
						outs.append(TypeRow(
							trimmed.rows[a].name,
							RefTree(1,SubsObject([
								SubRow(None,trimmed.rows[a].type.dpush(delta+toalc)),
								SubRow(None,substuff[refs[0]][0].simpush(tsimp)),
								SubRow(None,substuff[refs[0]][1].simpush(tsimp))
							],verdepth=alc),verdepth=alc)
						))
					elif len(refs) == 2:
						outs.append(TypeRow(
							trimmed.rows[a].name,
							RefTree(1,SubsObject([
								SubRow(None,trimmed.rows[a].type.dpush(delta+toalc)),
								SubRow(None,
									RefTree(3,SubsObject([
										SubRow(None,nurows[0]),
										SubRow(None,substuff[refs[0]][0].simpush(tsimp)),
										SubRow(None,substuff[refs[0]][1].simpush(tsimp)),
										SubRow(None,correctLambda([thad[0],"_"],nurows[-1],ScopeDelta([(1,nurows[-1].verdepth)]),verdepth=alc)),
										SubRow(None,outs[refs[0]].type.emptyinst(alc,inhuman[refs[0]])),
										SubRow(None,substuff[a][0].simpush(tsimp)),
									],verdepth=alc),verdepth=alc)
								),
								SubRow(None,substuff[a][1].simpush(tsimp))
							],verdepth=alc),verdepth=alc)
						))
					else:
						outs.append(TypeRow(
							trimmed.rows[a].name,
							RefTree(1,SubsObject([
								SubRow(None,trimmed.rows[a].type.dpush(delta+toalc)),
								SubRow(None,
									RefTree(3,SubsObject([
										SubRow(None,DualSubs([TypeRow(trimmed.rows[refs[i]].name,nurows[i]) for i in range(len(refs)-1)],verdepth=alc)),
										SubRow(None,SubsObject([
											SubRow(None,substuff[refs[i]][0].simpush(tsimp))
											for i in range(a)
										],verdepth=alc)),
										SubRow(None,SubsObject([
											SubRow(None,substuff[refs[i]][1].simpush(tsimp))
											for i in range(a)
										],verdepth=alc)),
										SubRow(None,correctLambda([thad,"_"],nurows[-1],ScopeDelta([(1,nurows[-1].verdepth)]),verdepth=alc)),
										SubRow(None,SubsObject([
											SubRow(None,outs[refs[i]].type.emptyinst(alc,inhuman[refs[i]]))
											for i in range(a)
										],verdepth=alc)),
										SubRow(None,substuff[a][0].simpush(tsimp)),
									],verdepth=alc),verdepth=alc)
								),
								SubRow(None,substuff[a][1].simpush(tsimp))
							],verdepth=alc),verdepth=alc)
						))
					aalc = longcount(trimmed.rows[a].name)
					alc += aalc
					delta = delta + ScopeDelta([(coflattenunravel(trimmed.rows[a].name,substuff[a][1],self.verdepth),),(-aalc,self.verdepth)])
				return DualSubs(outs,verdepth=self.verdepth)
		if self.core!=None: return component
		return None

class OperatorSet(Tobj):
	@initTobj
	def __init__(self,array,pos=None):
		self.array = array
		transferlines(self,pos)
	def needscarry(self):
		return False
	def verify(self,indesc,carry=None,reqtype=False,then=False):
		fulltree = []
		insert = fulltree
		for ind in self.array:
			if type(ind) is str:
				precnest  = indesc.precidence(ind)
				if precnest == None:
					raise LanguageError(self,"Operator not included in sneeze: "+ind)
				if insert == None:
					(prec,nesting) = precnest
					shift = fulltree
					while len(shift[-1]) == 3 and shift[-1][1] < prec or shift[-1][1] == prec and not nesting:
						shift = shift[-1][2]
					shift[-1] = (ind,prec,[shift[-1]])
					insert = shift[-1][2]
				else:
					urnary = (ind,precnest[0],[])
					insert.append(urnary)
					insert = urnary[2]
			else:
				insert.append(ind.verify(indesc,reqtype=True))
				insert = None
		def douparse(tree,carry=None):
			if len(tree) == 2: return tree
			p1 = [(None,douparse(u)) for u in tree[2]]
			errorcontext=[]
			ghi = indesc.symextract(tree[0],p1,reqtype=True,carry=carry,pos=self,errorcontext=errorcontext)
			if ghi == None:
				if len(errorcontext)==0:
					raise LanguageError(self,"operator not defined: "+str(tree[0]))
				raise LanguageError(self,"operator not defined for these arguments: "+str(tree[0])).callingcontext(errorcontext,-1)
			return ghi
		outp = douparse(fulltree[0],carry=carry)
		return outp if reqtype else outp[0]
	def prepr(self,context,trail):
		ssa = []
		for k in range(len(self.array)):
			if type(self.array[k]) is str: ssa.append(self.array[k])
			elif type(self.array[k]) is OperatorSet: ssa.append(context.red("(")+self.array[k].prepr(context,trail+[k])+context.red(")"))
			else: ssa.append(self.array[k].prepr(context,trail+[k]))
		return " ".join(ssa)
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		short = self.prepr(context,trail)
		if nonhtmllength(short+prepend)<=context.magic:
			out.append("\t"*indent+prepend+short+postpend)
			return
		rowprep = prepend
		for token in range(len(self.array)):
			if type(self.array[token]) is str:
				rowprep+=self.array[token]+" "
			else:
				if token == len(self.array)-1:
					self.array[token].pmultiline(context,trail+[token],out,indent,rowprep,postpend,callback=callback)
				else:
					self.array[token].pmultiline(context,trail+[token],out,indent,rowprep,"",callback=None)
				rowprep = ""


#link to:
	#more    -> increase stored variable and recalculate
	#replace -> prepr pass along line+row



def complicate(core,secrets,pos=None,names=None):
	# def _dbgExit(outp):
	# 	outp.hascorrectlinks()
	if len(secrets):
		if type(core) is ScopeComplicator:
			return ScopeComplicator(core.core,secrets+core.secrets,verdepth=core.verdepth-len(secrets),pos=pos,names=names+core.names)
		return ScopeComplicator(core,secrets,verdepth=core.verdepth-len(secrets),pos=pos,names=names)
	return core

def entrycomplicate(core,secrets,pos=None,names=None):
	# def _dbgExit(outp):
	# 	outp.hascorrectlinks()
	return complicate(core,secrets,pos,names)
	svod = core.verdepth-len(secrets)
	while True:
		if len(secrets)==0: return core
		if type(core) is ScopeComplicator:
			secrets = secrets+core.secrets
			names = names+core.names
			core = core.core
		conv = ScopeDelta()
		oust = []
		result = set()
		core.look(result)
		shiy = []
		# debugger = [copy.copy()]
		for i in reversed(range(len(secrets))):
			if svod+i in result:
				result.remove(svod+i)
				oust.insert(0,secrets[i])
				shiy.insert(0,names[i])
				if secrets[i].srows.isempty(): secrets[i].ob.look(result)
				else:
					secrets[i].srows.lookmemo = set()
					secrets[i].ob.advlook(result,secrets[i].srows)
			else:
				conv.append((-1,i+svod))
				for i in range(len(oust)): oust[i] = oust[i].dpush(ScopeDelta([(-1,i+svod)])) 
		if conv.isempty(): return ScopeComplicator(core,secrets,names=shiy,pos=pos,verdepth=svod)
		if not len(oust): return self.decode()
		secrets = oust
		core = core.dpush(conv)
		names = shiy
	return core.dpush(conv)
	


class DelayedComplication:
	def __init__(self,obj,srows=None):
		assert obj!=None
		self.ob = obj
		self.srows = ScopeDelta() if srows==None else ScopeDelta(srows.pushes)
		def _dbgTest():
			self.srows.objconforms(self.ob)
	def canbetranslated(self,pushes):
		self.ob.canbetranslated(self.srows+pushes)

	def assertValid(self):
		self.ob.canbetranslated(self.srows)
		# if self.ob.detect(self.srows):
		# 	# print("-=-=-=-=-=-=-")
		# 	# print(self.ob)
		# 	# print(self.ob.prepr(FormatterObject(None,fullrepresent=True,printcomplicators=True)))
		# 	# print(self.srows)
		# 	assert False
	def observeAT(self,target,exob=None):
		ldep = self.ob.verdepth+self.srows.lenchange
		if target==ldep and exob==None: return self.observe()
		# if self.srows.isempty() and exob==None:
		# 	return self.ob.simpush(SimpleDelta(target-ldep,min(ldep,target)))
		return self.ob.dpush(self.srows if target==ldep else self.srows+ScopeDelta([(target-ldep,min(ldep,target))]),exob=exob)
	# def delayAT(self,target):
	# 	if not hasattr(self,'dam'): self.dam = {}
	# 	else:
	# 		jar = self.dam.get(target)
	# 		if jar != None: return jar
	# 	ldep = self.ob.verdepth+self.srows.lenchange
	# 	jam = DelayedSub(self.ob,self.isSubOb(),self.srows+ScopeDelta([(target-ldep,min(ldep,target))]))
	# 	self.dam[target] = jam
	# 	return jam
	def reference(self,s):
		return DelayedComplication(self.ob.reference(s),self.srows)
	def __hash__(self):
		# print("\n\n")
		# print(type(self.ob))
		# print(tuple(self.srows.pushes))
		return hash((self.ob,self.srows))
	def __eq__(self,other):
		return type(other) is DelayedComplication and self.srows.pushes == other.srows.pushes and self.ob==other.ob
	def isSubOb(self):
		return isSubObPush(self.ob.isSubOb(),self.srows,inlen=self.ob.verdepth)



	def dpush(self,pushes):
		"""dbg_ignore"""
		# comb = ScopeDelta(
		# comb.isolate()
		return DelayedComplication(self.ob,self.srows+pushes)
	def observe(self):
		if self.srows.isempty(): return self.ob
		self.srows.tampdown()
		# if len(self.srows.pushes)==1 and len(self.srows.pushes[0])==2 and self.srows.pushes[0][0]>=0:
		# 	self.ob = self.ob.simpush(SimpleDelta(self.srows.pushes[0][0],self.srows.pushes[0][1]))
		# 	self.srows = ScopeDelta([])
		# 	return self.ob
		self.ob = self.ob.dpush(self.srows)
		self.srows = ScopeDelta([])
		return self.ob
	def setSafety(self,safe):
		self.ob.setSafety(safe-self.srows.lenchange)
	def getSafety(self):
		return self.ob.getSafety()+self.srows.lenchange
	def setVerified(self):
		self.ob.setVerified()


class ScopeComplicator(Tobj):
	def innertrim(self,si=None,disgrace=None):#ScopeComplicator
		return entrycomplicate(self.core.innertrim(si=si,disgrace=disgrace),self.secrets,names=self.names)

	def isfrozen(self):
		return self.core.isfrozen()
	def __eq__(self,other):
		return type(other) is ScopeComplicator and self.secrets==other.secrets and self.core==other.core
	def __hash__(self):
		if self.cachehash != None: return self.cachehash
		self.cachehash = hash((tuple(self.secrets),self.core))
		return self.cachehash
	@initTobj
	def __init__(self,core,secrets,verdepth=None,pos=None,names=None):
		self.core = core
		self.secrets = secrets
		self.verdepth = verdepth
		self.cache = None
		self.cachehash = None
		self.names = names
		if len(names) != len(secrets):
			print(names)
			print(secrets)
		assert len(names) == len(secrets)
		# self.legaltracking = True
		transferlines(self,pos)
		def _dbgTest():
			assert type(self.secrets) is list
			# for i in names:
			# 	assert i!=None
			for g in self.secrets:
				if g!=None:
					assert isinstance(g,DelayedComplication)
			assert len(self.secrets)
		# def _dbgTest():
		# 	result = set()
		# 	self.core.look(result)
		# 	for i in reversed(range(len(self.secrets))):
		# 		if self.verdepth+i in result:
		# 			result.remove(self.verdepth+i)
		# 			if self.secrets[i].srows.isempty(): self.secrets[i].ob.look(result)
		# 			else:
		# 				self.secrets[i].srows.lookmemo = set()
		# 				self.secrets[i].ob.advlook(result,self.secrets[i].srows)
		# 		else:
		# 			assert False


			# self.decode()

	def paredown(self):
		# while True:
		# 	if len(self.secrets)==0: return self.core
		# 	if type(self.core) is ScopeComplicator:
		# 		self.secrets = self.secrets+core.secrets
		# 		self.names = self.names+core.names
		# 		self.core = core.core
		conv = ScopeDelta()
		oust = []
		result = set()
		self.core.look(result)
		shiy = []
		# debugger = [copy.copy()]
		for i in reversed(range(len(self.secrets))):
			if self.verdepth+i in result:
				result.remove(self.verdepth+i)
				oust.insert(0,self.secrets[i])
				shiy.insert(0,self.names[i])
				if self.secrets[i].srows.isempty(): self.secrets[i].ob.look(result)
				else:
					self.secrets[i].srows.lookmemo = set()
					self.secrets[i].ob.advlook(result,self.secrets[i].srows)
			else:
				conv.append((-1,i+self.verdepth))
				for i in range(len(oust)): oust[i] = oust[i].dpush(ScopeDelta([(-1,i+self.verdepth)])) 
		if conv.isempty(): return self
		if not len(oust): return self.decode()
		# try:
		self.core = self.core.dpush(conv)
		# except DpushError:
		# 	print()
		# 	print(self.verdepth)
		# 	print(len(self.secrets))
		# 	print(conv)
		# 	print(self.core)
		# 	assert False
		self.names = shiy
		self.secrets = oust
		if type(self.core) is ScopeComplicator:
			self.secrets = self.secrets+core.secrets
			self.names = self.names+core.names
			self.core = core.core

		assert len(self.secrets)==len(self.names)
		return self



	def semavail(self,mog=False):
		return self.decode().semavail(mog)
	def correction(self):
		return ScopeDelta([(-len(self.secrets),self.verdepth)])
	def decode(self):
		if self.cache != None: return self.cache
		self.cache = self.core.dpush(self.correction()).decode()
		# if not self.legaltracking: assert False
		return self.cache
	def compare(self,other,odsc=None,thot=None,extract=None,lefpush=None,rigpush=None):
		return self.core.compare(other,odsc,thot,extract,self.correction() if lefpush==None else self.correction()+lefpush,rigpush)
	def look(self,result,lowerbound=False):
		self.core.look(result,lowerbound=lowerbound)
		for i in reversed(range(len(self.secrets))):
			if self.verdepth+i in result:
				result.remove(self.verdepth+i)
				if self.secrets[i].srows.isempty(): self.secrets[i].ob.look(result,lowerbound=lowerbound)
				else:
					self.secrets[i].srows.lookmemo=set()
					self.secrets[i].ob.advlook(result,self.secrets[i].srows,lowerbound=lowerbound)
				

		# if self.src==None: result.add(self.name)
		# else: self.src.look(result)
	def advlook(self,result,pushes,lowerbound=False):
		self.core.advlook(result,pushes,lowerbound=lowerbound)
		for i in reversed(range(len(self.secrets))):
			pushes.lookmemo.discard(self.verdepth+i)
			if self.verdepth+pushes.lenchange+i in result:
				result.remove(self.verdepth+pushes.lenchange+i)
				madra = self.secrets[i].srows+pushes
				madra.lookmemo = set()
				self.secrets[i].ob.advlook(result,madra,lowerbound=lowerbound)
	def simpush(self,alo):
		short = alo.mem2.get(id(self));
		if short!=None: return short
		fukko = ScopeDelta([(alo.amt,alo.lim)])
		res = ScopeComplicator(self.core.simpush(alo),[g.dpush(fukko) for g in self.secrets],verdepth=self.verdepth+alo.amt,pos=self,names=self.names)
		alo.mem2[id(self)] = res
		return res


	def hascorrectlinks(self,yooj={}):
		yooj = copy.copy(yooj)
		for x in range(len(self.secrets)): yooj[self.verdepth+x] = self.secrets[x].isSubOb()
		self.core.hascorrectlinks(yooj)

	def canbetranslated(self,pushes):
		if alreadycanbetranslated(self,pushes): return
		for j in self.secrets: j.canbetranslated(pushes)
		self.core.canbetranslated(pushes)



	def dpush(self,pushes,exob=None,frozen=False,selective=None):
		early = pushes.getmemo(self,exob,frozen)
		if early!=None: return early
		# res,sof = semi_complicate_dpush(self.verdepth+pushes.lenchange,self.secrets,pushes)
		# mom = complicate(self.core.dpush(pushes+sof,exob=exob,frozen=frozen,selective=selective),res,pos=self)
		bok = [secret.dpush(pushes) for secret in self.secrets]
		res = complicate(self.core.dpush(pushes,exob=exob,frozen=frozen,selective=selective),bok,pos=self,names=self.names)
		if hasattr(pushes,'delaymemo'):
			for k in range(self.verdepth+pushes.lenchange,self.verdepth+pushes.lenchange+len(self.secrets)):
				pushes.delaymemo.pop(k,None)
			# pushes.delaymemo = {k:v for (k,v) in pushes.delaymemo.items() if k<self.verdepth+pushes.lenchange}
		if selective==None: pushes.setmemo(self,exob,frozen,res)
		return res
	def detect(self,ranges):
		if self.core.detect(ranges): return True
		if hasattr(ranges,'precal'): ranges.precal = [a for a in ranges.precal if a<self.verdepth]
		return False

	def writefile(self,file):
		self = self.paredown()
		if type(self) is not ScopeComplicator: return self.writefile(file)
		file.writeChar("J")
		file.writeNum(len(self.secrets))
		for oe in self.secrets: oe.observe().writefile(file)
		file.writeStrInc([a if type(a) is str else "no_name" for a in self.names])
		self.core.writefile(file)
	def prepr(self,context,trail):
		if not context.printcomplicators: return self.decode().prepr(context,trail)
		if type(self.core) is DualSubs and context.shouldtrim(trail) and any(row.obj!=None for row in self.core.rows):
			self = entrycomplicate(self.core.trimallnonessential(),self.secrets,names=self.names)
		self = self.paredown()
		if type(self) is not ScopeComplicator: return self.prepr(context,trail)
		res = []
		for k in range(len(self.secrets)):
			try:
				word = context.newcolors(self.names[k])
				res.append(self.names[k] if type(self.names[k]) is str else "no_name")
				# res.append(self.names[k]+":="+self.secrets[k].observe().prepr(context,trail+[]+[k]))
				context = context.addbits(word)
			except DpushError: pass
		return context.red("[")+",".join(res)+context.red("]")+self.core.prepr(context,trail+[len(self.secrets)])
	def pmultiline(self,context,trail,out,indent,prepend,postpend,callback=None):
		if not context.printcomplicators: return self.decode().pmultiline(context,trail,out,indent,prepend,postpend,callback=callback)
		if type(self.core) is DualSubs and context.shouldtrim(trail) and any(row.obj!=None for row in self.core.rows):
			self = entrycomplicate(self.core.trimallnonessential(),self.secrets,names=self.names)
		self = self.paredown()
		if type(self) is not ScopeComplicator: return self.pmultiline(context,trail,out,indent,prepend,postpend,callback=callback)
		def calls(context,out,prepend):
			self.core.pmultiline(context,trail+[len(self.secrets)],out,indent,prepend,postpend,callback=callback)
		res = []
		for a in range(len(self.secrets)):
			try:
				# if 
				# res.append(a.observe())
				res.append(None)
				# res.append(u_type(self.verdepth+len(res)))
			except DpushError: pass
		pmultilinecsv(context,trail,out,indent,res,prepend+context.red("["),context.red("]"),lamadapt=lambda n,x:self.names[n],callback=calls,delim=context.red(","),seplist=self.names)


def hasfixes(si):
	if type(si) is list:
		return any(hasfixes(s) for s in si)
	return si!=None and '*****' in si

@v_args(meta=True)
class MyTransformer(Transformer):
	def start(self,children,meta):
		deps = []
		rows = []
		for child in children[:-1]:
			if type(child) is tuple:
				rows.append(child)
			else:
				deps.append(child)
		return (deps,rows,children[-1])
	def precrow(self,children,meta):
		if type(children[-1]) is dict:
			return (children[:-1],children[-1])
		return (children,{'associate':'left'})
	def leftassoc(self,children,meta):
		return {'associate':'left'}
	def rightassoc(self,children,meta):
		return {'associate':'right'}
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
			if type(children[1]) is Strategy: children[0][1]['contractible'] = children[1].getbecsafety()
			return TypeRow(children[0][0],children[1],obj,children[0][1])
		obj = None
		if len(children)>1:
			obj = children[1]
		return TypeRow(None,children[0],obj,{'silent':False,'contractible':None if type(children[0]) is not Strategy else children[0].getbecsafety()})
	def inferreddeclaration(self,children,meta):
		ty = None if len(children)<3 else Strategy(args=children[1],type=None,pos=meta)
		if type(ty) is Strategy: children[0][1]['contractible'] = ty.getbecsafety()
		return TypeRow(children[0][0],ty,children[-1],children[0][1])
	def silentmarker(self,children,meta):
		return {'silent':True,'contractible':None}
	def infermarker(self,children,meta):
		return {'silent':False,'contractible':None}
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
		args = []
		for j in children[lim:]:
			args += j.subs
		return RefTree(name,SubsObject(args,pos=meta) if len(args) else None,src,pos=meta)
	def lamb(self,children,meta):
		coal = []
		for c in children[:-1]:
			coal+=c
		if hasfixes(coal):
			raise LanguageError(meta,"Lambdas do not support automatic unpacking.")
		return Lambda(coal,children[-1],pos=meta)
	def directive(self,children,meta):
		for i in children[0]:
			if type(i) is not str or '*****' in i:
				raise LanguageError(meta,"Invalid renaming directive. Directive on left side must not be recursive.")
		if len(children) == 1:
			return (children[0],children[0])
		return (children[0],children[1])
	# def renamer(self,children,meta):
		

	def template(self,children,meta):
		state=0
		for c in children[1:]:
			ns = 1 if type(c) is tuple else 2 if type(c) is TypeRow else 3 if type(c) is SubRow else None
			if state>ns: raise LanguageError(meta,"Templates always must follow this order: renaming directives, then mixins, then substitutions.")
			state = ns
		return Template(
			children[0],
			([j for l in children[1:] if type(l) is tuple for j in l[0]],[j for l in children[1:] if type(l) is tuple for j in l[1]]),
			[c for c in children[1:] if type(c) is TypeRow],
			[c for c in children[1:] if type(c) is SubRow],
		pos=meta)


	# def mixedsubs(self,children,meta):
	# 	return ([c for c in children if type(c) is TypeRow],[c for c in children if type(c) is SubRow])

	def strategy(self,children,meta):
		args = []
		for j in children[:-1]:
			args += j.rows
		ouou = Strategy(DualSubs(args,pos=meta),children[-1],pos=meta)
		if len(children)>2: ouou.becsafety = len([i for i in children[0].rows if i.obj==None])
		return ouou
	def string(self,children,meta):
		if prefix_postfix_check.match(str(children[0])): return str(children[0]).replace('+','*****')
		return str(children[0]).replace("'","")
	def operators(self,children,meta):
		return OperatorSet(children,pos=meta)
	def subsobject(self,children,meta):


		return SubsObject(children,pos=meta)
	def wsubsobject(self,children,meta):
		if len(children):
			if len(children[0].subs) == 1 and children[0].subs[0].name==None:
				return children[0].subs[0].obj
			else:
				return children[0]
		else:
			return SubsObject(pos=meta)

	def wsafesubsobject(self,children,meta):
		if len(children):
			return children[0]
		else:
			return SubsObject(pos=meta)

	def dualsubs(self,children,meta):
		return DualSubs(children,pos=meta)
	def wdualsubs(self,children,meta):
		return children[0] if len(children) else DualSubs(pos=meta)
class Untransformer:
	def __init__(self,dict,subdict,head=0):
		self.dict = dict
		self.postob = subdict
		self.head = head
	def update(self,scope):
		for s in scope:
			if s.obj!=None:
				self.dict[self.head] = s.obj
			self.head+=1
		return self
	def isolate(self):
		return Untransformer(copy.copy(self.dict),self.postob,self.head)
	def emptywrite(self,amt):
		return Untransformer(copy.copy(self.dict),{},self.head+amt)
	def getat(self,ind):
		if ind in self.postob: return self.postob[ind]
		if ind not in self.dict: return None
		# ob = self.dict[ind]
		# res = DelayedSub(ob,ob.isSubOb(),ScopeDelta([(self.head-ob.verdepth,ob.verdepth)]))
		res = self.dict[ind].observe()
		self.postob[ind] = res
		return res
	def objwrite(self,ty,ds,si):
		# assert type(ds) is not DelayedComplication
		if si==None: hoe = [ds]
		else: hoe = amorphwidereference(ds,ty,si)
		for t in range(len(hoe)):
			if hoe[t]!=None:
				self.dict[self.head+t] = DelayedComplication(hoe[t])
		self.head += len(hoe)
		self.postob = {}

# global_debugging = False

class DataBlockWriter:
	def __init__(self,filename):
		self.writer = io.BufferedWriter(io.FileIO(filename, 'w'))
	def writeChar(self,char):
		self.writer.write(char.encode())
	def writeStr(self,str):
		self.writer.write((str+"'").encode())
	def writeNum(self,num):
		self.writer.write((str(num)+"'").encode())
	def writeStrInc(self,inc):
		if type(inc) is list:
			self.writeChar("'")
			for j in inc: self.writeStrInc(j)
			self.writeChar('"')
		else:
			self.writeStr(inc)
	def writeNumInc(self,inc):
		if type(inc) is list:
			self.writeChar("'")
			for j in inc: self.writeNumInc(j)
			self.writeChar('"')
		else:
			self.writeNum(inc)
	def writeHeader(self,md5,deps,ob):
		self.writeStr(md5)
		self.writeNum(len(deps))
		for a,b in deps:
			self.writeStr(a)
			self.writeStr(b)
		for o in ob:
			o.observe().writefile(self)
class DataBlockTransformer:
	def __init__(self,block,head):
		self.block = block
		self.head = head
	def readChar(self):
		self.head+=1
		return self.block[self.head-1]
	def readStr(self):
		oh=self.head
		while self.block[self.head]!="'":self.head+=1
		self.head+=1
		return self.block[oh:self.head-1]
	def readNum(self):
		return int(self.readStr())
	def readStrInc(self):
		g = self.readStr()
		if g!='': return g
		vo = []
		while True:
			if self.block[self.head]=='"':
				self.head+=1
				return vo
			vo.append(self.readStrInc())
	def readNumInc(self):
		g = self.readStr()
		if g!='': return int(g)
		vo = []
		while True:
			if self.block[self.head]=='"':
				self.head+=1
				return vo
			vo.append(self.readNumInc())
	def generic(self,depth):
		code = self.readChar()
		if   code == "A":#reftree,src==None
			name = self.readNum()
			return RefTree(
				name=name,
				core=depth.getat(name),
				verdepth=depth.head
			)
		elif code == "B":#reftree,src!=None
			name = self.readNum()
			return RefTree(
				name=name,
				src=self.generic(depth),
				verdepth=depth.head
			)
		elif code == "H":#reftree,src!=None
			name = self.readNum()
			return RefTree(
				name=name,
				args=self.SubsObject(depth),
				core=depth.getat(name),
				verdepth=depth.head
			)
		elif code == "I":#reftree,src!=None
			name = self.readNum()
			return RefTree(
				name=name,
				args=self.SubsObject(depth),
				src=self.generic(depth),
				verdepth=depth.head
			)
		elif code == "C": return self.DualSubs(depth)
		elif code == "D": return self.DualSubs(depth,origin=(self.generic(depth),self.readNumInc(),self.readNumInc()))
		elif code == "E": return self.Strategy(depth)
		elif code == "F": return self.SubsObject(depth)
		elif code == "G": return self.Lambda(depth)
		elif code == "J": return self.ScopeComplicator(depth)
		else: assert False
	def TypeRow(self,depth):
		code = self.readChar()
		name = self.readStrInc() if code in 'acegi' else None
		ty   = self.generic(depth)
		obj  = self.generic(depth) if code in 'ab' else None
		silent   = code in 'ghij'
		contract = self.readNum() if code in 'efij' else None
		return TypeRow(name,ty,obj,{'silent':silent,'contractible':contract})

	def ScopeComplicator(self,depth):

		depth = depth.isolate()
		oh = depth.head
		lim = self.readNum()
		rows = []
		for row in range(lim):
			ob = self.generic(depth)
			rows.append(DelayedComplication(ob))
			depth.objwrite(None,ob,None)
		names = self.readStrInc()
		return ScopeComplicator(self.generic(depth),rows,verdepth=oh,names=names)

	def DualSubs(self,depth,then=False,origin =None):
		if not then: depth = depth.isolate()
		odh = depth.head
		lim = self.readNum()
		rows = []
		for row in range(lim):
			rows.append(self.TypeRow(depth))
			depth.objwrite(rows[-1].type,rows[-1].obj,rows[-1].name)
		return DualSubs(rows,origin =origin,verdepth=odh)
	def Strategy(self,depth):
		odh = depth.head
		depth = depth.isolate()
		args = self.DualSubs(depth,then=True)
		return Strategy(args,self.generic(depth),verdepth=odh)
	def SubsObject(self,depth):
		lim = self.readNum()
		return SubsObject([SubRow(None,self.generic(depth)) for k in range(lim)],verdepth=depth.head)
	def Lambda(self,depth):
		si = self.readStrInc()
		outp = Lambda(si,self.generic(depth.emptywrite(longcount(si))),verdepth=depth.head)
		return outp
	def readHeader(self):
		md5 = self.readStr()
		lim = self.readNum()
		ok = []
		for c in range(lim):
			ok.append((self.readStr(),self.readStr()))
		return (md5,ok)
	def readScope(self,depth):
		rows = []
		while self.head!=len(self.block):
			rows.append(self.TypeRow(depth).delay())
			depth.objwrite(rows[-1].type.observe(),None if rows[-1].obj==None else rows[-1].obj.observe(),rows[-1].name)
		return rows
class FileLoader:
	def __init__(self,overrides=None,l=None,basepath="",redoAll=False,verbose=False,buildpath=None):
		self.lark = l
		if l == None:
			with open("core.lark", "r") as f:
				self.lark = Lark(f.read(),parser='lalr',propagate_positions=True)
		self.basepath = basepath
		self.buildpath = buildpath if buildpath!=None else basepath
		self.redoAll = redoAll
		self.verbose = verbose
		self.overrides = overrides if overrides!=None else {}

		self.md5s = {}

		self.deps    = []
		self.cumu    = []
		self.lengths = {}
		self.subdeps = {}


	def onlyinclude(self,deps):
		pexclude = []
		hs=0
		for dep in self.deps:
			if dep not in deps: pexclude.append((self.lengths[dep],hs))
			hs+=self.lengths[dep]
		return ScopeDelta(pexclude)

	def filloutdeps(self,deps):
		hoa = []
		for dep in deps:
			for nd in self.subdeps[dep]:
				if nd not in hoa: hoa.append(nd)
			hoa.append(dep)
		return hoa

	def arrangeTo(self,fve,targdeps,ver):
		def _dbgEnter():
			# for pi in targdeps:
			# 	assert pi in fve
			count = 0
			for k in fve: count+=self.lengths[k]
			for s in range(len(ver)): ver[s].setSafetyrow(s+count)
		def _dbgExit(ou):
			count = 0
			for k in targdeps: count+=self.lengths[k]
			for s in range(len(ou)): ou[s].setSafetyrow(s+count)

		tub = []
		hs = 0
		for i in range(len(targdeps)):
			ms = hs
			for l in range(i,len(fve)):
				if fve[l]==targdeps[i]:
					if l==i: break
					tub.append((hs,i_of,ms,self.lengths[targdeps[i]]))
					swp=fve[l]
					fve[l]=fve[i]
					fve[i]=swp
					break
				l_of = self.lengths[fve[l]]
				if l==i: i_of = l_of
				ms+=l_of
			else:
				fve.insert(i,targdeps[i])
				tub.append((self.lengths[targdeps[i]],hs))
			hs += self.lengths[targdeps[i]]
		if len(fve)>len(targdeps):
			tub.append((-sum(self.lengths[b] for b in fve[len(targdeps):]),hs))
		return ver if len(tub)==0 else [a.dpush(ScopeDelta(tub)) for a in ver]
		

	def getdepsas(self,deps):
		out = []
		sof = []
		for d in range(len(deps)):
			hs = 0
			for w in range(len(self.deps)):
				if self.deps[w]==deps[d]:
					out = out + self.arrangeTo(self.deps[:w],deps[:d],self.cumu[hs:hs+self.lengths[self.deps[w]]])
					break
				hs += self.lengths[self.deps[w]]
			else: assert False
		return out


	def load(self,filename,circular=None,redo=False):
		# global global_debugging
		# def _dbgExit(ou):
		# 	assert filename in self.deps
		circular = [] if circular == None else circular
		if filename in circular: raise LanguageError(None,"Cyclic import: "+filename)
		if filename in self.deps: return
		if filename in self.overrides.keys(): document = self.overrides[filename]
		else:
			if not os.path.exists(self.basepath+filename): raise LanguageError(None,"Could not import file: "+filename).setfile(filename if len(circular)==0 else circular[-1])
			with open(self.basepath+filename,"r",encoding='utf-8') as f: document = f.read()
		md5 = hashlib.md5(document.encode()).hexdigest()
		self.md5s[filename] = md5
		if not (self.redoAll or redo) and os.path.exists(self.buildpath+filename+".ver"):
			with open(self.buildpath+filename+".ver","r") as f:
				dbt = DataBlockTransformer(f.read(),0)
				try:
					fmd5,fdeps = dbt.readHeader()
				except: pass
				else:
					if fmd5==md5:
						valid = True
						for dep,dmd5 in fdeps:
							self.load(dep,circular+[filename])
							if self.md5s[dep]!=dmd5:
								valid = False
								break
						if valid:
							if True:
								print("beginning load: ",self.buildpath+filename)
								fve = [a[0] for a in fdeps]
							# try:
								ver = self.arrangeTo(fve,self.deps,dbt.readScope(Untransformer({},{}).update(self.getdepsas(fve))))
							# except: pass
							# else:
								self.cumu += ver
								self.deps.append(filename)
								self.lengths[filename] = len(ver)
								self.subdeps[filename] = [p[0] for p in fdeps]
								print("loaded: ",self.buildpath+filename)
								return
		if os.path.exists(self.buildpath+filename+".ver"): os.remove(self.buildpath+filename+".ver")
		try:
			# raise LanguageError(None,"DUDUDUDUDDUDU")
			deps,rows,ob = MyTransformer().transform(self.lark.parse(document))
		except UnexpectedInput as u:
			u.file = filename
			raise u
		except VisitError as e:
			if isinstance(e.__context__, LanguageError):
				e.__context__.file = filename
				raise e.__context__
			raise e

		for dep in range(len(deps)):
			for d in range(dep):
				if deps[d] == deps[dep]: raise LanguageError(None,"Duplicate import").setfile(filename)
			self.load(deps[dep],circular+[filename])

		print("beginning verify: ",self.basepath+filename)
		olen = len(self.cumu)

		try:
			# if filename=="lattice_extensions.ax": global_debugging = True
			obj,ncumu = ob.verify(ScopeObject(self.cumu,prpush=self.onlyinclude(deps),oprows=ContextYam(rows)),then=True)

		except LanguageError as u: raise u.setfile(filename)

		deps = self.filloutdeps(deps)
		print("arranging ",filename," from ",self.deps,"to ",deps)

		tosave = self.arrangeTo(copy.copy(self.deps),deps,ncumu.flat[olen:])

		DataBlockWriter(self.buildpath+filename+".ver").writeHeader(md5,[(a,self.md5s[a]) for a in deps],tosave)
		print("verified: ",self.basepath+filename)
		self.cumu = ncumu.flat
		self.deps.append(filename)
		self.lengths[filename] = len(self.cumu)-olen
		self.subdeps[filename] = deps

		# def _dbgTest():

		# DataBlockWriter("temporary.ver").writeHeader(md5,[],self.cumu)
		# with open("temporary.ver","r") as f:
		# 	dbt = DataBlockTransformer(f.read(),0)
		# dbt.readHeader()
		# ver = dbt.readScope(Untransformer({}))
		# DualSubs(self.cumu).assertcomp(DualSubs(ver))
		# one = DualSubs(self.cumu).prepr(FormatterObject(None,fullrepresent=True))
		# two = DualSubs(ver).prepr(FormatterObject(None,fullrepresent=True))
		# if one != two:
		# 	print("\n\n"*5,one)
		# 	print("\n\n"*2,two)
		# 	assert False


		# print("cross verified ",len(self.cumu))

# try:
# 	compilefiles({"grouptheory.ax"},verbose=True)
# except LanguageError as u:
# 	u.tohtml()
# 	raise u


def _dbgTest():
	print("OSIDJFOIDJFS")
	try:
		FileLoader(verbose=True,basepath="/Users/parkerlawrence/dev/agi/",buildpath="/Users/parkerlawrence/dev/agi/build/",redoAll=True).load("turing.ax",redo=True)
		# FileLoader(verbose=True,basepath="/Users/parkerlawrence/dev/agi/",buildpath="/Users/parkerlawrence/dev/agi/build/",redoAll=False).load("builtin.ax",redo=True)
	except Exception as u:
		if hasattr(u,'xaxException'):
			u.tohtml()
		raise u



# echo 'except Exception as u:'         >> temporary.py
# echo " if hasattr(u,'xaxException'):" >> temporary.py
# echo '  u.tohtml()'                   >> temporary.py


#if mangle_ue starts taking up a lot of time, remember that you can store ful/semavail on a property so yo don't have ot unwrap<><><>
#you could also create a separate unwrap function for trimming and dpushing at the same time to avoid all those extra properties you dont need.<><><>


#scopecomplicator should have some way to preserve secrets if it's obvious that they are the same. isSubOb is your friend.<><>

#subsobject will need to redetect(tuple of src)                            on dpush...<>

#really should crack down on (0,x) depth pushes.

#<>make it so a.b macros work a little more dilligently...

#if the time spent inside the compare function accounts for a significant portion of the runtime, then you should implement a list of previous substitutions to compare instead
#	those ladders may be subbed out already. they vanish when dpush clobbers them.



#<><> rewrite widereference to use asdualsubsNonspecific (and any other possible places- look for mangle_UE )



#<><><> translate memoization and dpush memoization.
#<><><> also make unwrap memoization provably valid.


#trimallnonessential should do a better job of what it does.<>


# <><><> capture invalidsplits.


#<> use less threes- when all previous inferred objects have subs already in extract you don't need a three.(3)
#<> crack down on (0,x) and (a,b,c,d) where b+d = c+d-a

#<><>mangles rely on 1 reftrees always having three parameters- what about fibers???









