import sys

COUNT = int(sys.argv[1])

lines = sys.stdin.readlines()

data = [[]] * COUNT

def parse_line(ln):
    return [float(x) for x in ln.strip().split('\t')]

def avg_line(data):
    data.sort()
    return (sum(data)/len(data), min(data), max(data))

def add_pointwise(ls):
    return [sum([l[i] for l in ls]) for i in range(0,len(ls[0]))]

def total_lines(lns):
    data = [parse_line(ln) for ln in lns]
    avg_line(add_pointwise(ls))

for ln in range(0, len(lines)/COUNT):
    for i in range(0,COUNT):
        data[i] = data[i] + [avg_line(parse_line(lines[COUNT*ln+i]))]

total = []
for ln in range(0, len(lines)/COUNT):
    total = total + [avg_line(total_lines(lines[COUNT*ln+i:COUNT*(ln+1)-1]))]


print "\\pgfplotstableread{"
print "n\t" + "\t".join(["d%d\td%d-min\td%d-max" % (i,i,i)
                         for i in range(0, COUNT)])
start = 3
for n in range(0,len(data[0])):
    dta = "\t".join(["%f\t%f\t%f" % (data[i][n][0], data[i][n][1], data[i][n][2])
                     for i in range(0, COUNT)])
    print "%d\t%f\t%f\t%f\t%s" % (start, total[n][0], total[n][1], total[n][2], dta)
    start = start + 1
print "}{\\datatable}"




# print "%% vm_compute"
# print "\\addplot"
# start = 5
# for t in vm:
#     print "(%d,%f)" % (start, t)
#     start = start + 1
# print ";"
