



def hella(F):
	def wrapper(*args):
		return F(*args)
	return wrapper



# @hella
# def yopwop(a,b):
# 	print(a,b)
# 	assert False

# @hella
# def wopwop(a,b):
# 	print(a,b)
# 	yopwop(a,b)


def _dbgEnter_t1(self):
	print("dbg ent")

class ho:
	@hella
	def t1(self,n,e):
		assert n!=0 or e
		if n == 0: return
		print("t1")
		self.t1(n-1,e)

class ho3:
	@hella
	def t1(self,e):
		print("t11111")
		g = ho()
		g.t1(2,e)


g = ho3()
g.t1(True)
g.t1(False)