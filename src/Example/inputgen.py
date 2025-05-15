
data="""

[
  {
    "count" : 1,
    "word": "HELLO"
  },
  {
    "bonus":2,
    "count": 3,
    "word": "BREAK"
  }
]

--

[{"count":1,"word":"A"}]

--

[]

"""

files = data.split("--")
pos=[0]
for f in files[:-1]:
  pos.append(pos[-1]+len(f))
lengths=map(len,files)
k=zip(lengths,pos)

print("type NFiles =",len(files))
print("files :: Vec NFiles (Int,Int)")
print("files =",":>".join(map(repr,k))+":>Nil")
print("fileData :: Vec %d Char" % len("".join(files)))
print("fileData =",":>".join(map(repr,"".join(files)))+":>Nil")
