import os
import time

path = "./test/Test_Case"

def test_solver():
  # get the test file
  cnf_files = os.listdir(path)
  print(cnf_files)

  # create the output file
  output_path = f"./result/{time.strftime('%m%d%H%M%S')}"

  with open(output_path, "w") as f:
    f.write(f"test cases in: {path}\n")
    for file in cnf_files:
      print("executing " + file)
      output = os.popen(f"python3 solvepy3.py {path}/{file}").read()
      # save the output to a file
      f.write(file + "\n")
      f.write(output)
      f.write("\n")

test_solver()
