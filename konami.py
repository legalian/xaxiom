import sublime, sublime_plugin
from lark import Lark, UnexpectedInput, Transformer, v_args, InlineTransformer, Tree
import os
import sys
from .structures import *
from .metastructures import *
import functools

import copy
import re





@v_args(meta=True)
class MyTransformer(Transformer):
	def objstrategy(self,children,meta):
		# print(type(meta))
		# assert False
		return ObjStrategy(parsed=children,pos=meta)
	def treeref(self,children,meta):
		return ObjKindReferenceTree(parsed=children,pos=meta)
	def union(self,children,meta):
		return ObjKindUnionSet(parsed=children,pos=meta)
	def andtype(self,children,meta):
		return ObjKindTypeUnion(parsed=children,pos=meta)


	def object(self,children,meta):
		return ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindTypeUnion(pos=meta,variables=[ObjStrategy(pos=meta,ty=ObjKindReferenceTree(pos=meta,name="NOT",args=[a])) for a in children])])
	def objectinter(self,children,meta):
		return ObjKindTypeUnion(pos=meta,variables=[ObjStrategy(pos=meta,ty=a,name=a.name.lower() if a.name != None and a.name[0].isupper() else None) for a in children])


	def lognot(self,children,meta):
		return ObjKindReferenceTree(pos=meta,name="NOT",args=[children[0]])




	def compchain(self,children,meta):
		svart = []
		g=0
		while g < len(children)-1:
			sym = str(children[g+1].data)
			if   sym == "ltsym":   start = ObjKindReferenceTree(pos=meta,name="GT",args=[children[g+2],children[g+0]])
			elif sym == "lteqsym": start = ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindReferenceTree(pos=meta,name="GT",args=[children[g+0],children[g+2]])])
			elif sym == "eqsym":   start = ObjKindReferenceTree(pos=meta,name="EQ",args=[ObjKindReferenceTree(pos=meta,name="AFF"),children[2],children[0]])
			elif sym == "gteqsym": start = ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindReferenceTree(pos=meta,name="GT",args=[children[g+2],children[g+0]])])
			elif sym == "gtsym":   start = ObjKindReferenceTree(pos=meta,name="GT",args=[children[g+0],children[g+2]])
			else: assert False
			svart.append(start)
			g = g + 2

		assert len(svart) > 0
		if len(svart) == 1: return svart[0]
		return ObjKindTypeUnion(pos=meta,variables=[ObjStrategy(pos=meta,ty=svar) for svar in svart])

	def scopemop(self,children,meta):
		return children


	def objectsum(self,children,meta):
		sumo = []
		nexneg = False
		for z in children:
			if   str(z) == "-": nexneg = True
			elif str(z) == "+": nexneg = False
			elif nexneg: sumo.append(ObjKindReferenceTree(pos=meta,name="AINVERSE",args=[z]))
			else: sumo.append(z)
		a = sumo[0]
		for b in sumo[1:]: a = ObjKindReferenceTree(pos=meta,name="ADD",args=[a,b])
		return a
	def objectprod(self,children,meta):
		a = children[0]
		for b in children[1:]: a = ObjKindReferenceTree(pos=meta,name="MULT",args=[a,b])
		return a
	# def sub(self,children,meta):
	# 	return ObjKindReferenceTree(pos=tree,name="ADD",args=[tree.children[0],ObjKindReferenceTree(pos=tree,name="AINVERSE",args=[tree.children[1]])])
	# def prod(self,children,meta):
	# 	return ObjKindReferenceTree(pos=tree,name="MULT",args=[tree.children[0],tree.children[1]])
	def customeq(self,children,meta):
		return ObjKindReferenceTree(pos=meta,name="EQ",args=[children[1],children[0],children[2]])
	def customneq(self,children,meta):
		return ObjKindReferenceTree(pos=meta,name="NOT",args=[ObjKindReferenceTree(pos=meta,name="EQ",args=[children[1],children[0],children[2]])])

	def label(self,children,meta):
		# print(tree)
		# return str(tree)
		# return tree
		return str(children[0])


	def statement(self,children,meta):
		# print(tree,"opopop")
		# print(the,"opopop")
		return Statement(pos=meta,parsed=children)
	def strategy(self,children,meta):
		return Strategy(pos=meta,parsed=children)
	def multistrat(self,children,meta):
		return multistrat(children)




# class BuildAxiomCommand(sublime_plugin.TextCommand):
# 	def run(self):
# 		print("hello world")

class BuildAxiomCommand(sublime_plugin.ViewEventListener,sublime_plugin.TextCommand):
	def run(self,kwar,action="parse"):
		# action = kwar.get("action","parse")#view.run_command('build_axiom',{'action':'clear'})
		if action == "parse":
			self.update_syntax_phantoms()
		if action == "clear":
			print("clearing...")
			self.phantom_set.update([])
			self.phantom_set.update([])

	def on_post_save(self):
		self.update_syntax_phantoms()


	def __init__(self, view):
		self.view = view
		self.phantom_set = sublime.PhantomSet(view)
		self.timeout_scheduled = False
		self.needs_update = False

		# self.tooltipranges = []
		# self.insertpoints = []

		self.curtree = None

		self.syntaxphantoms = []
		self.selectorphantoms = []


		f = open(os.path.dirname(os.path.realpath(__file__))+"/core.lark", "r")
		self.l = Lark(f.read(),parser='lalr', propagate_positions=True)#
		f.close()

		self.update_phantoms()

	@classmethod
	def is_applicable(cls, settings):
		syntax = settings.get('syntax')
		return syntax == 'Packages/myplugin/axiom.sublime-syntax'
	   
	def on_query_completions(self, prefix, locations):
		# elements = ET.parse(
		#     urllib.request.urlopen(GOOGLE_AC % prefix)
		# ).getroot().findall("./CompleteSuggestion/suggestion")

		sugs = [["hoe","wak"],["asda","wawejk"],["hrhr","ohoh"]]

		return (sugs,sublime.INHIBIT_WORD_COMPLETIONS|sublime.INHIBIT_EXPLICIT_COMPLETIONS)


	def update_selector_phantoms(self):

		self.selectorphantoms = []
		if self.curtree is None: return
		ranges = []
		for den in self.view.sel():
			if den.a!=den.b:
				ranges.append(den.begin())
				continue
			#do work here

		diagno = []
		scope = Scope([])
		diagnostics(self.curtree,scope,ranges,self.view,diagno)
		for diag in diagno:
			if diag[1] == None:
				error = '<span style="color:#FF00FF">~error~ = '+str(diag[0])+' . . . \n(~nosig~)</span>'
			else:
				if diag[5] == 1:
					error = '<span style="color:#FF00FF">'+str(diag[2])+' = '+str(diag[0])+' . . . \n('+str(diag[1])+') (found by name only)</span>'
				else:
					error = '<span style="color:#FF00FF">'+str(diag[2])+' = '+str(diag[0])+' . . . \n('+str(diag[1])+')</span>'
			self.selectorphantoms.append(sublime.Phantom(
				sublime.Region(self.view.text_point(diag[3],diag[4])),#carry cig type
				error,
				sublime.LAYOUT_BELOW
			))
		self.update_phantoms()


	def update_syntax_phantoms(self):
		self.syntaxphantoms = []


		# Don't do any calculations on 1MB or larger files
		if self.view.size() < 2**20:
			document = self.view.substr(sublime.Region(0,self.view.size()))
			# self.tooltipranges = []
			# self.insertpoints = []
			# for empty in re.finditer('[~]\\s*', document, re.MULTILINE):
			# 	self.tooltipranges.append((empty.start()+1,empty.end()))
				# self.insertpoints.append(empty.start()+1)
			# self.insertpoints.sort()

			# self.insertpoints = [0] + self.insertpoints + [len(document)]
			# document = '\xA5'.join([document[self.insertpoints[i]:self.insertpoints[i+1]] for i in range(len(self.insertpoints)-1)])
			try:
				ahah = MyTransformer().transform(self.l.parse(document))
				#ahah = self.l.parse(document)

				bank = ahah.children[0]
				objec = ahah.children[1]

				errors = ErrorObject([])
				objec.verify(StratSeries([ObjStrategy(upcast=b) for b in bank]),ObjKindReferenceTree(name="U"),errors)
				print(objec)
				print(errors.rer)

				# print(parseobjkind(ahah.children[1]))
				# attempt = Strategy(parsed=ahah)
				# for node in bank:
				self.curtree = Strategy(args=bank,ty=Statement([],name="U",id=0,local=0),name="AxiomBank")


				self.syntaxphantoms = syntaxreports(self.curtree,self) + metasyntaxreports(errors,self)

				# self.curtree = attempt
			except UnexpectedInput as u:
				self.syntaxphantoms.append(sublime.Phantom(
					sublime.Region(self.view.text_point(u.line-1,u.column-1)),
					'<span style="color:red">█Syntax:</span>',
					sublime.LAYOUT_INLINE
				))
				self.curtree = None
		self.update_phantoms()
	def update_phantoms(self):
		self.phantom_set.update([])
		self.phantom_set.update(self.syntaxphantoms+self.selectorphantoms)



	# def handle_timeout(self):
	# 	self.timeout_scheduled = False
	# 	if self.needs_update:
	# 		self.needs_update = False
	# 		self.update_phantoms()

	def on_selection_modified(self):
		self.update_selector_phantoms()

	# def on+
	# def on_modified(self):
	# 	# Call update_phantoms(), but not any more than 10 times a second
	# 	if self.timeout_scheduled:
	# 		self.needs_update = True
	# 	else:
	# 		sublime.set_timeout(lambda: self.handle_timeout(), 100)
	# 		self.update_syntax_phantoms()








