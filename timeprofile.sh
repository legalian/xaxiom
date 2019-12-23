

sed 's/from \.lark import/from lark import/g' simplifier.py > temporary.py
echo 'compilefiles({"grouptheory.ax","builtin.ax"},verbose=True,redoAll=False,basepath="/Users/parkerlawrence/dev/agi/")' >> temporary.py
python3 -m cProfile -o temp.dat temporary.py
# python3 temporary.py
rm temporary.py
snakeviz temp.dat

