import os, sys, subprocess

os.system("make")
os.system("dist/rep2rep " + sys.argv[1])
os.chdir("output/latex")
os.system("pdflatex " + sys.argv[2] + " > /dev/null")
