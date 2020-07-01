
import os
import sys
if "Sublime Text" in __file__:
  from .lark import Lark, UnexpectedInput, Transformer, v_args, InlineTransformer, Tree
  from .simplifier import FileLoader,htmlatlocation
  import functools
  import copy
  import re

  import sublime, sublime_plugin

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

      self.activeError = None

      self.syntaxphantoms = []

      f = open(os.path.dirname(os.path.realpath(__file__))+"/core.lark", "r")
      self.l = Lark(f.read(),parser='lalr', propagate_positions=True)#
      f.close()

      self.update_phantoms()

      
    @classmethod
    def is_applicable(cls, settings):
      syntax = settings.get('syntax')
      return syntax!=None and syntax.endswith('axiom.sublime-syntax')

    def update_syntax_phantoms(self):
      self.syntaxphantoms = []

      # Don't do any calculations on 1MB or larger files
      if self.view.size() < 2**20:
        document = self.view.substr(sublime.Region(0,self.view.size()))
        print("compiling...")
        basepath,filename = os.path.split(os.path.realpath(self.view.file_name()))
        basepath += "/"
        buildpath = basepath+"build/" if os.path.isdir(basepath+"build") else basepath
        self.activeError=None
        try: FileLoader(overrides={filename:document},l=self.l,basepath=basepath,buildpath=buildpath).load(filename)
        except Exception as u: self.activeError = u
        self.regen()
      else:
        self.syntaxphantoms = []
        self.phantom_set.update([])
        self.phantom_set.update([])

    def regen(self):
      basepath,filename = os.path.split(os.path.realpath(self.view.file_name()))
      self.syntaxphantoms = []
      u = self.activeError
      if u==None: return self.update_phantoms()
      if isinstance(u,UnexpectedInput):
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
      elif hasattr(u,'xaxException'):
        if u.file == filename:
          self.syntaxphantoms.append(sublime.Phantom(
            sublime.Region(self.view.text_point(u.row-1,u.column-1)),
            u.tohtml(),
            sublime.LAYOUT_BELOW,
            u.callback(self.regen)
          ))
        else:
          self.syntaxphantoms.append(sublime.Phantom(
            sublime.Region(self.view.text_point(0,0)),
            htmlatlocation(basepath,u.file,u.row,u.column,u.tohtml()),
            sublime.LAYOUT_BELOW,
            u.callback(self.regen)
          ))
      else: raise u
      self.update_phantoms()

    def update_phantoms(self):
      self.phantom_set.update([])
      self.phantom_set.update(self.syntaxphantoms)






