project_path = "/flash/java-benchmarks/JDV/target/MyFace/"
file_path = project_path + "chains"
out = project_path + "result_key.txt"
keyWord = "apache"

gcs = []
ssSet = []
with open(file_path, 'r') as file:
    gc = []
    for line in file:
        if line == "\n":
            flag = False
            for gadget in gc:
                if keyWord in gadget:
                    flag = True
                    break
            if flag:
                gcs.append(gc)
            gc = []
        else:
            gc.append(line)

with open(out, 'w') as fileout:
    for gc in gcs:
        for gadget in gc:
            fileout.write(gadget)
        fileout.write("\n")
    fileout.write("total gc count: " + str(len(gcs)))