import sublime, sublime_plugin
from lark import Lark, UnexpectedInput, Transformer, v_args, InlineTransformer, Tree
import os
import sys


from .transformer import MyTransformer

# from .nexus import MyTransformer
# from .nexus import *

from .simplifier import *

import functools

import copy
import re



# reloadself()



# from myplugin.transformer

# print("\n".join([i for i in vars(nexus).keys()]))
# print(vars(nexus))

# print(vars(sys.modules["myplugin.transformer"]))


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
		# global MyTransformer, StratSeries, ErrorObject
		# reloadself()
		# MyTransformer = vars(sys.modules["myplugin.transformer"])["MyTransformer"]
		# StratSeries = vars(sys.modules["myplugin.metastructures"])["StratSeries"]
		# ErrorObject = vars(sys.modules["myplugin.metastructures"])["ErrorObject"]

		
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

	# def on_query_completions(self, prefix, locations):
	# 	# elements = ET.parse(
	# 	#     urllib.request.urlopen(GOOGLE_AC % prefix)
	# 	# ).getroot().findall("./CompleteSuggestion/suggestion")

	# 	sugs = [["hoe","wak"],["asda","wawejk"],["hrhr","ohoh"]]

	# 	return (sugs,sublime.INHIBIT_WORD_COMPLETIONS|sublime.INHIBIT_EXPLICIT_COMPLETIONS)


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



				
				# errors = ErrorObject()

				# cheat = StratSeries([ObjStrategy(upcast=b) for b in bank])
				# cheat = cheat.verify(StratSeries([],exverified=True),errors)
				print("your monkey matching doesnt work")
				print("need multiple different alternate comparators and also lazy-flatten-callbacks.")
				print("maybe lookahead to figure out if types should be supplied(or obj==None), sparing yourself an observation.")
				#|+5|a(b,c,d)
				print("--=-=-=-=--momomomo=-=-=-=-=-=-==--=>>>>>>")
				# try:
				nobh = ahah[1].verify(ScopeObject([],oprows=ahah[0]))
				print(nobh)
				print("--=-=-=-=--=-=-=-=-=-=-==--=>>>>>>")
				# except ErrorObject as u:
				# 	pass
				# except RuntimeError:
				# 	print("RECURSION DEPTH EXCEEDED")


				print()
				print()
				print()
				print(task)
				print(ErrorObject.rer)

				# print(parseobjkind(ahah.children[1]))
				# attempt = Strategy(parsed=ahah)
				# for node in bank:
				self.curtree = None

				#syntaxreports(self.curtree,self)
				self.syntaxphantoms = ErrorObject.reports(self,wclist)

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








