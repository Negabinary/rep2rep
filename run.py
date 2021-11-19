import os, sys, subprocess

os.chdir("output/latex")
if os.path.exists(sys.argv[2][:-3] + "pdf"):
    os.remove(sys.argv[2][:-3] + "pdf")
if os.path.exists(sys.argv[2]):
    os.remove(sys.argv[2])
os.chdir("../..")
os.system("make")
os.system("dist/rep2rep " + sys.argv[1])
os.chdir("output/latex")
os.system("pdflatex " + sys.argv[2] + " > /dev/null")
