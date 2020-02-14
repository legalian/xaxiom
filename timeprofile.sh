

sed 's/from \.lark import/from lark import/g' simplifier.py > temporary.py
echo 'FileLoader(verbose=True,basepath="/Users/parkerlawrence/dev/agi/",buildpath="/Users/parkerlawrence/dev/agi/build/",redoAll=False).load("lattice_extensions.ax")' >> temporary.py
python3 -m cProfile -o temp.dat temporary.py
# python3 temporary.py
# python3 debugger.py temporary.py


rm temporary.py
snakeviz temp.dat




# python3 -m cProfile -o temp.dat debugger.py temporary.py