import os
directories = [
    "Grading/Program1",
    "Grading/Program2",
    "Grading/Program3",
    "Grading/Program4",
    "Grading/Program5",
    "Grading/Program7",
]
target_directories = [
    "program1",
    "program2",
    "program3",
    "program4",
    "program5",
    "program7",
]

# create target directories
for target_directory in target_directories:
    if not os.path.exists(target_directory):
        os.makedirs(target_directory)

for indx, directory in enumerate(directories):
    # each directory contains sub directories "shuffled-XX"
    for subdir in os.listdir(directory):
        if "shuffled" not in subdir:
            continue
        try:
            # each sub directory contains a file called handin-text.rkt
            handin_text = os.path.join(directory, subdir, "handin-text.rkt")
            #move file to programx directory
            os.rename(handin_text, os.path.join(target_directories[indx], subdir + ".rkt"))
        except:
            print("Error in", subdir)
