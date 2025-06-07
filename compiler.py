import sys
import os

sys.path.append(os.path.join(os.path.dirname(__file__), 'main-py'))

from BrainFun import default__ as BrainFun

def verify_valid_loop(command):
    count = 0
    for i in command:
        if i == '[':
            count += 1
        elif i == ']':
            count -= 1
        if count < 0:
            return False
    return count == 0

if __name__ == "__main__":
    bf_code = input("What is the BF Program? ")
    bf_code = list(bf_code)
    for i in bf_code:
        if i not in ['+', '-', ',', '.', '>', '<', '[', ']']:
            print("Invalid BF Program. Exiting...")
            exit()
    if verify_valid_loop(bf_code) == False:
        print("Invalid BF Program. Exiting...")
        exit()
    input_data = list(input("What is the user input? "))
    for i in input_data:
        if ord(i) < 0 or ord(i) > 255:
            print("Invalid User Input. Exiting...")
            exit()

    # Compile the program
    program = BrainFun.CompileFromString(bf_code, input_data)
    ir = BrainFun.Compile(program)

    # Print the intermediate representation object

    BrainFun.IRtoString(ir)