



class Example:
	def __init__(self):
		self.hello = 2

	def goober(self,x):
		def _dbgEnter():
			# assert x<20
			assert x>=0
		def _dbgExit(val):
			assert type(val) is str


		for j in range(self.hello):
			pass
		if self.hello != 1:
			return ("ya")
		else:
			return None

	def foobar(self):
		print(self.goober(9999))



def _dbgTest():
	example = Example();
	example.foobar()
	example.foobar()
	example.foobar()
	example.foobar()
	example.hello = 1
	example.foobar()

