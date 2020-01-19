import sublime, sublime_plugin
from .lark import Lark, UnexpectedInput, Transformer, v_args, InlineTransformer, Tree
import os
import sys
from .simplifier import FileLoader,htmlatlocation
import functools
import copy
import re


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
		return syntax.endswith('axiom.sublime-syntax')

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

			print("compiling...")
			basepath,filename = os.path.split(os.path.realpath(self.view.file_name()))
			basepath += "/"
			try: FileLoader(overrides={filename:document},l=self.l,basepath=basepath).load(filename)
			except UnexpectedInput as u:
				if u.file == filename:
					self.syntaxphantoms.append(sublime.Phantom(
						sublime.Region(self.view.text_point(u.line-1,u.column-1)),
						'<span style="color:red">█Syntax:</span>',
						sublime.LAYOUT_INLINE
					))
				else:
					self.syntaxphantoms.append(sublime.Phantom(
						sublime.Region(self.view.text_point(0,0)),
						htmlatlocation(basepath,u.file,u.line,u.column,'<span style="color:red">Syntax error</span>'),
						sublime.LAYOUT_INLINE
					))
			except Exception as u:
				if not hasattr(u,'xaxException'): raise u
				if u.file == filename:
					self.syntaxphantoms.append(sublime.Phantom(
						sublime.Region(self.view.text_point(u.row-1,u.column-1)),
						u.tohtml(),
						sublime.LAYOUT_BELOW
					))
				else:
					self.syntaxphantoms.append(sublime.Phantom(
						sublime.Region(self.view.text_point(0,0)),
						htmlatlocation(basepath,u.file,u.row,u.column,u.tohtml()),
						sublime.LAYOUT_BELOW
					))
			self.curtree = None
		self.update_phantoms()
	def update_phantoms(self):
		self.phantom_set.update([])
		self.phantom_set.update(self.syntaxphantoms+self.selectorphantoms)








	# def on_selection_modified(self):
	# 	self.update_selector_phantoms()








