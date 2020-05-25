

sed 's/from \.lark/from lark/g' simplifier.py > temporary.py
# echo 'FileLoader(verbose=True,basepath="/Users/parkerlawrence/dev/agi/",buildpath="/Users/parkerlawrence/dev/agi/build/",redoAll=False).load("lattice_extensions.ax",redo=True)' >> temporary.py


# echo 'try:'                           >> temporary.py
echo 'FileLoader(verbose=True,basepath="/Users/parkerlawrence/dev/agi/",buildpath="/Users/parkerlawrence/dev/agi/build/",redoAll=True).load("peano.ax",redo=True)' >> temporary.py
# echo 'except Exception as u:'         >> temporary.py
# echo " if hasattr(u,'xaxException'):" >> temporary.py
# echo '  u.tohtml()'                   >> temporary.py
# echo ' raise u'                       >> temporary.py

# python3 -m cProfile -o temp.dat temporary.py

# python3 temporary.py
python3 debugger.py temporary.py


# rm temporary.py
# snakeviz temp.dat
# 



# python3 -m cProfile -o temp.dat debugger.py temporary.py