import json
import pandas as pd
import matplotlib.pyplot as plt

# JSON files to be imported, generate this with `lake exe graph physlean.xdot_json`
# See `https://github.com/leanprover-community/import-graph` for more info
graphFile = "physlean.xdot_json"

# Dictionary with keys ['name', 'directed', 'strict', '_subgraph_cnt', 'objects', 'edges']
physLean = json.load(open(graphFile))

# Dictionary with keys ['_gvid', 'name', 'fillcolor', 'label', 'shape', 'style']
files = physLean['objects']
# Dictionary with keys ['_gvid', 'tail', 'head']
# The 'tail' of an import arrow is the file being imported and the 'head' is the file doing the importing
imports = physLean['edges']

# Creates a dataframe with an entry for each file with its name, the indices of the files it imports, and the files that import it
physLean = pd.DataFrame([{'name':f['name'], 'imports':[], 'dependents':[]} for f in files])

# Total number of files in the project
numFiles = len(physLean)

# Adds the subject of the file (the name of the folder under PhysLean) to the datafram
physLean['subject'] = physLean.name.apply(lambda str: str.split('.')[1] if len(str.split('.')) > 1 else "PhysLean" )

# The list of all current subjects in PhysLean
subjectList = physLean.subject.unique()

# Builds the imports and dependents
for i in imports:
    physLean.dependents.loc[i['tail']].append(i['head'])
    physLean.imports.loc[i['head']].append(i['tail'])

# Returns the name of a file with a given index
def toName(index):
    return list(physLean.name.loc[index])

# Returns a list of the files imported by the file of a given index
def nameImports(index):
    return toName(physLean.imports.loc[index])

# Returns a list of the files that import the file of a given index
def nameDependents(index):
    return toName(physLean.dependents.loc[index])

# Returns the index of the file with the provided name
def toIndex(name):
    return physLean.index[physLean.name == name].tolist()

# Initialize the transitive import list
transImports = [None for i in range(len(physLean))]

# Generates the transitive imports for a given index
def genTransImports(index):
    # The transImports were already generated, skip
    if transImports[index] != None:
        return
    # The transImports starts with a copy of the direct imports
    transImports[index] = physLean.imports.loc[index].copy()
    # Adds the transImports of all direct imports, after possibly generating those lists
    for i in physLean.imports.loc[index]:
        genTransImports(i)
        transImports[index] += transImports[i]
    # Removes duplicate entries
    transImports[index] = list(set(transImports[index]))

# Generates the full list of transitive imports
for i in range(len(physLean)):
    genTransImports(i)

# Initialize the transitive dependents list
transDependents = [None for i in range(len(physLean))]

# Generates the transitive dependents for a given index
def genTransDependents(index):
    # The transDependents were already generated, skip
    if transDependents[index] != None:
        return
    # The transDependents starts with a copy of the direct dependents
    transDependents[index] = physLean.dependents.loc[index].copy()
    # Adds the transDependents of all direct dependents, after possibly generating those lists
    for i in physLean.dependents[index]:
        genTransDependents(i)
        transDependents[index] += transDependents[i]
    # Removes duplicate entries
    transDependents[index] = list(set(transDependents[index]))

# Generates the full list of transitive dependents
for i in range(len(physLean)):
    genTransDependents(i)

# Add transitive imports to dataframe
physLean['transImports'] = transImports
# Add transitive dependents to dataframe
physLean['transDependents'] = transDependents
# Add the number of transitive imports to dataframe
physLean['numTransImps'] = physLean.transImports.apply(len)
# Add the number of transitive dependents to dataframe
physLean['numTransDeps'] = physLean.transDependents.apply(len)

# Adds a measure of importance of a file to dataframe
# Importance is the product of % files transitively imported and % files transitively dependent
physLean['importance'] = physLean.apply(lambda x: (x.numTransImps/numFiles)*(x.numTransDeps/numFiles), axis=1)

# Plot the number of transitive dependents versus number of transitive imports
'''
plt.plot(physLean.numTransImps, physLean.numTransDeps, 'o')
plt.xlabel("# Transitive Imports")
plt.ylabel("# Transitive Dependents")
plt.show()
'''

# Plot a histogram of the importance of each file
'''
plt.hist(physLean.importance)
plt.xlabel("Importance")
plt.show()
'''

