from math import log, exp
from itertools import count
from operator import itemgetter
from nltk import Tree, FreqDist
from nltk.sem import LogicParser as lp
from bitpar import BitParChartParser
from treelink import TransformationDOP, removeforcepos, undecorate_with_ids,\
	linked_subtrees_to_probabilistic_rules, minimal_linked_subtrees

top = "QUERY"
nl = [
	Tree("QUERY", ['what is', Tree("FORM", ['the smallest', Tree("FORM",
		['state']), Tree("FORM", ['by', 'area'])])]),
	Tree("QUERY", ["how many", Tree("FORM", ['states', Tree("FORM", ['border',
		Tree("FORM", ['the state', Tree("FORM", ['that borders', Tree("FORM",
		['the most', Tree("FORM", ['states'])])])])])])]),
	Tree("QUERY", ['how many', Tree("FORM", ['major', Tree("FORM",
		['cities'])]), 'are', Tree('FORM', ['in', Tree("FORM", ['states',
		Tree("FORM", ['bordering', Tree("FORM", ['texas'])])])])])
	]

# todo: parse logical forms with grammar of meaning representation
sem = [
	Tree("QUERY", ["answer(x1,", Tree("FORM(x1)", [r"\x1.smallest(x2,(",
		Tree("FORM(x1)", [r"\x1.state(x1)"]), ',',
		Tree('FORM(x1,x2)', [r"\x1.\x2.area(x1,x2)"]), '))']), ')']),
	Tree("QUERY", ['answer(x1,', Tree("FORM", ['count(x2,(',
		Tree("FORM", ['state(x2),', Tree("FORM", ['next_to(x2,x3),',
		Tree("FORM", ['most(x3,x4,(', Tree("FORM", ['state(x3),',
		Tree("FORM", ['next_to(x3,x4),', Tree("FORM", ['state(x4)'])])]),
		'))'])])]), '),x1)']), ')'])
	# [...]
	]

top = "TOP"
nl = [
	Tree("(TOP (WHNP@1 what) (SQ (VBZ does) (NP@2 a bunny) (VP@3 do)) (. ?))"),
	Tree("(TOP (WHNP@4 what) (SQ (VBZ does) (NP@5 a duckie) (VP@6 say)) (. ?))")
	]

sem = [
	Tree("(TOP (SPEECH-ACT@1 whquestion) (CLAUSE@3 (do X)) (CLAUSE@2 (animal bunny)))"),
	Tree("(TOP (SPEECH-ACT@4 whquestion) (CLAUSE@6 (do X)) (CLAUSE@5 (animal duckie)))")
	]

"""
0 (TOP (WHNP what) (SQ (VBZ does) (NP a bunny) (VP do)) (. ?))
1 (WHNP what)
2 (SQ (VBZ does) (NP a bunny) (VP do))
3 (VBZ does)
4 (NP a bunny)
5 (VP do)
6 (. ?)

0 (TOP (SPEECH-ACT whquestion) (CLAUSE (do X)) (CLAUSE (animal bunny)))
1 (SPEECH-ACT whquestion)
2 (CLAUSE (do X))
3 (do X)
4 (CLAUSE (animal bunny))
5 (animal bunny)
"""

# get indices for links
links = []
for t1, t2 in zip(nl, sem):
	lt1 = [n for n,t in sorted(enumerate(t1.subtrees(lambda x: "@" in x.node)), key=itemgetter(1))]
	lt2 = [n for n,t in sorted(enumerate(t2.subtrees(lambda x: "@" in x.node)), key=itemgetter(1))]
	links.append(zip(lt1, lt2))

#get linked trees
mlsts1 = [[(subtrees1[a], subtrees2[b]) for a,b in link]
			for subtrees1, subtrees2, link
			in ((list(t1.subtrees()), list(t2.subtrees()), l)
				for t1, t2, l in zip(nl, sem, links))]

# remove other linked subtrees
mlsts = []
for mlst, link in zip(mlsts1, links):
	newmlst = []
	for treepair, l in zip(mlst, link):
		ts = ()
		for n,t in enumerate(treepair):
			m = [a[n] for a in mlst]
			tree = t.copy(True)
			for x in t.treepositions()[1:][::-1]:
				if tree[x] in m: del tree[x][:]
			ts += (tree,)
		newmlst.append(ts)
	mlsts.append(newmlst)

def dotranslate(sent, parser, tdop):
	# todo: tokenize sentence by maximizing unigram probabilities
	# in training corpus, to detect multiword units
	sent = sent.split()

	# parse sentence with bitpar, gives an n-best list
	try:
		parsetrees1 = list(parser.nbest_parse(sent))
	except Exception as e:
		parsetrees1 = []
		print n, "parsing failed", e
		return

	# undo binarization and auxilary POS tags introduced to accomodate bitpar:
	parsetrees = FreqDist()
	for tree in parsetrees1:
		tree.un_chomsky_normal_form()
		parsetrees.inc(removeforcepos(tree).freeze(), count=tree.prob())

	# for each parsetree, get a list of translations
	resultfd = {}
	for m, tree in enumerate(parsetrees):
		print "parse tree", tree
		#pdb.set_trace()
		for nn, (result, prob) in enumerate(
			tdop.get_mlt_deriv_multi(tree, smoothing=True, verbose=False)):
			if not result: continue
			key = (undecorate_with_ids(result).freeze(),
				sum(1 if "@" in a.node else 0 for a in result.subtrees()))
			resultfd[key] = resultfd.setdefault(key, 0.0) + prob
	return resultfd.popitem()

def remspaces(tree):
	for a in tree.treepositions('leaves'):
		tree[a] = tree[a].replace(" ", "_")
	return tree

tdop = TransformationDOP()
for n, tree1, tree2, mlst in zip(count(), nl, sem, mlsts):
	print n
	# todo: replace minimal_linked_subtrees with a function
	# that takes alignments (such as from giza) and deduces
	# subtree links from that
	tdop.add_to_grammar(
		linked_subtrees_to_probabilistic_rules( #mlst,
		minimal_linked_subtrees(remspaces(tree1), tree2),
		limit_subtrees=1000))

rules, lexicon = tdop.get_grammar(bitpar=True, freqfn=sum)
parser = BitParChartParser(rules, lexicon, cleanup=True,
									rootsymbol=top, n=100)
print "\ngrammar:"
for a,b in tdop.grammardict.items():
	print a,
	for x,y in b.items():
		print y,
		for z in x: print z,
	print

for n, tree1, tree2, mlst in (): #zip(count(), nl, sem, mlsts):
	print n
	for a,b in mlst:
		print a, "<=>", b
	print
	for a,b in minimal_linked_subtrees(remspaces(tree1), tree2):
		print a, "<=>", b

sent = "what does a duckie do ?"
print '\nparsing:', sent
try:
	(tree, n), prob = dotranslate(sent, parser, tdop)
	print n, exp(prob), tree
except: print "no parse"
exit()

# interface
while True:
	print "sentence:",
	sent = raw_input()
	try:
		(tree, n), prob = dotranslate(sent, parser, tdop)
		print n, prob, tree
	except: print "no parse"
