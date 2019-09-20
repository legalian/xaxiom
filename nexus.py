
# import imp
# import sys

# def reloadself():
# 	vodolo = {}
# 	for module in ["debugging","transformer","metametastructures","metastructures","structures"]:
# 		module_name = "myplugin."+module
# 		if module_name in sys.modules:
# 			del sys.modules[module_name]
# 		__import__(module_name)
# 		vodolo.update(dict([(k,v) for k,v in vars(sys.modules[module_name]).items() if not k.startswith("__")]))
# 	for module in ["transformer","metametastructures","metastructures","structures","debugging"]:
# 		module_name = "myplugin."+module
# 		vars(sys.modules[module_name]).update(vodolo)


