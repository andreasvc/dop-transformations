from bitpar import BitParChartParser
from memoize import memoize
from nltk import Tree, WeightedProduction, WeightedGrammar,\
	ViterbiParser, FreqDist, WordNetLemmatizer, Nonterminal
from itertools import chain, combinations
from collections import defaultdict
from sys import argv

USE_LEMMATIZATION = True
wnl = WordNetLemmatizer() 

current_id = 0

class TransformationDOP:
	def __init__(self):
		self.grammardict = defaultdict(FreqDist)

	def add_to_grammar(self, mlsts, source="left"):
		# Adds the minimal linked subtrees (mlsts) to the grammar.
		for (lefttree, righttree, links, count) in mlsts:
			if source == "right":
				lefttree, righttree = righttree, lefttree
			righttree = righttree.freeze()
			links = tuple(links)
			flattened_tree = my_flatten(lefttree)
			#flattened_tree.chomsky_normal_form()
			index = filter(lambda x: len(x.rhs()) > 0, flattened_tree.productions())[0]
			if index in self.grammardict:
				self.grammardict[index].inc((righttree, links), count)
			else:
				self.grammardict[index].inc((righttree, links), count)

	def print_grammar(self):
		for (key, value) in self.grammardict.items():
			print "Source rule: %s\n\n" % key
			for ((tree, links), count) in value.items():
				print "  Tree: %s\n" % tree
				print "  Links: %s\n" % links
				print "  Count: %s\n\n" % count
			print

	def get_grammar(self, freqfn=max, prob=True, bitpar=False, root="S"):
		# Returns a PCFG. (Use freqfn=max for most likely derivation, prob=sum for most likely parse)
		# grammar = []
		#for (key, value) in self.grammardict.items():
		#	grammar.append(WeightedProduction(key.lhs(), key.rhs(), prob=freqfn([count for tree, links, count in value])))
		# return grammar
		grammar = [ WeightedProduction(key.lhs(), key.rhs(), prob=freqfn(count for (tree, links), count in value.items())) for key, value in self.grammardict.items() ]
		if prob:
			fd = FreqDist()
			for key in grammar:
				fd.inc(key.lhs(), count=key.prob())
			#fd = FreqDist((key.lhs(), key.prob()) for key in grammar)
			if bitpar:
				lexicon = [key.rhs()[0] for key in self.grammardict if not isinstance(key.rhs()[0], Nonterminal)]
				grammar = []
				for key, value in self.grammardict.items():
					count = freqfn(count for (t,l), count in value.items())
					tmp = forcepos(production_to_tree(key))
					tmp.chomsky_normal_form()
					for a in tmp.productions():
						if len(a.rhs()):
							grammar.append(("%s\t%s" % (str(a.lhs()), "\t".join(map(str, a.rhs()))), count))
				return grammar, lexicon
				return [("%s\t%s" % (str(key.lhs()), "\t".join(map(str, key.rhs()))), freqfn(count for (tree, links), count in value.items())) for key, value in self.grammardict.items()], lexicon
			else:
				grammar = [WeightedProduction(key.lhs(), key.rhs(), 
					prob=freqfn(count for (tree, links), count in value.items()) / float(fd[key.lhs()]))
					for key, value in self.grammardict.items()]
				return WeightedGrammar(Nonterminal(root), grammar)
		else:
			return grammar


	def get_mlt_deriv(self, tree):
		# Returns the most likely transformation of tree (based on the most likely derivation).
		top_production = tree.productions()[0]

		# Finds the most likely right hand side of top-production
		"""count = 0
		for (curtree, curlinks), curcount in self.grammardict[top_production].items():
			if curcount > count:
				righttree, links, count = curtree, curlinks, curcount"""
		if top_production in self.grammardict:
			righttree, links = self.grammardict[top_production].max()
		else: raise ValueError

		new_subtrees = []
		for a in tree:
			if isinstance(a, Tree):
				new_subtrees.append(self.get_mlt_deriv(a))

		# Add new subtrees
		frontiers = frontier_nodes(righttree)
		target = Tree.convert(righttree)
		for n, index in enumerate(links):
			#print index, n, target[frontiers[index][1]], '/', new_subtrees[n]
			target[frontiers[index][1]] = new_subtrees[n]
		return target


def minimal_linked_subtrees(tree1, tree2):
	# Takes out shared subtrees from tree1 and tree2, until nothing is left.
	# Then decomposes the shared subtrees into rules linked to themselves.
	# Then links the remaining (unmatchable) part of tree1 to tree2.

	shared_subtrees = True # Are there any shared subtrees?
	linked_subtrees = []
	equivalents = []
	tree1 = tree1.copy(True) # (deep copy)
	tree2 = tree2.copy(True) # (deep copy)

	while(shared_subtrees):
		max_shared_subtree_size = 0 # The size of the maximal shared subtree
		max_shared_subtree = None
		lemmatized_equivalents = None
		for (parent1, num1, i) in my_subtrees(tree1):
			for (parent2, num2, j) in my_subtrees(tree2):
				if i == j and isinstance(i, Tree):
					# check if larger than current maximal tree, etc.
					if len(leaves_and_frontier_nodes(i)) > max_shared_subtree_size:
						max_shared_subtree_size = len(leaves_and_frontier_nodes(i))
						max_shared_subtree = (i, parent1, num1, parent2, num2)

		# If no subtree is found yet, find an 'almost-match' (e.g. a
		# conjugation)
		if USE_LEMMATIZATION and max_shared_subtree == None:
			for (parent1, num1, i) in my_subtrees(tree1):
				if isinstance(i, Tree) and len(i) == 1 and type(i[0]) == str:
					for (parent2, num2, j) in my_subtrees(tree2):
						if (isinstance(j, Tree) and
							i.node == j.node and i.node[0] == 'V' and # starts with V
							len(j) == 1 and type(j[0]) == str and
							wnl.lemmatize(i[0], 'v') == wnl.lemmatize(j[0], 'v')):
								lemmatized_equivalents = (i, j, parent1, num1,
									parent2, num2)

		# Remove the shared subtree from the tree...
		if max_shared_subtree:
			(tree, parent1, num1, parent2, num2) = max_shared_subtree
			# Decorate tree with ids.
			tree = decorate_with_ids(tree)
			parent1[num1] = Tree(tree.node, []) # tree.node
			parent2[num2] = Tree(tree.node, []) # tree.node
		elif lemmatized_equivalents:
			(i, j, parent1, num1, parent2, num2) = lemmatized_equivalents
			(i, j) = decorate_pair(i, j)
			parent1[num1] = Tree(i.node, [])
			parent2[num2] = Tree(j.node, [])
		
		if lemmatized_equivalents:
			equivalents.append((i, j))
		elif max_shared_subtree == None:
			shared_subtrees = False
		else:
			linked_subtrees.append(tree)
	print "Phase -1"
	# Decompose linked subtrees into minimal subtrees (so far: these always are
	# PCFG-rules)
	minimal_subtrees = []
	for i in linked_subtrees:
		for j in i.productions():
			if len(j.rhs()) > 0:
				minimal_subtrees.append(
					(production_to_tree(j), production_to_tree(j)))
	print "Phase 0"
	for (x, y) in equivalents:
		minimal_subtrees.append((x, y))

	minimal_subtrees.append((tree1, tree2))
	return minimal_subtrees

def linked_subtrees_to_probabilistic_rules(linked_subtrees):
	# Add 'links' between leaf nodes.
	print "Phase 1..."
	linked_subtrees2 = []
	for (t1, t2) in linked_subtrees:
		l1 = filter(lambda x: (isinstance(x, Tree) and '@' in x.node), leaves_and_frontier_nodes(t1))
		l2 = filter(lambda x: (isinstance(x, Tree) and '@' in x.node), leaves_and_frontier_nodes(t2))
		# Very ugly, but might be needed to guarantee the right outcome...
		a = [(l1.index(x), l2.index(x)) for x in l1]
		a.sort()
		a = [x[1] for x in a] 
		linked_subtrees2.append((t1, t2, a))
	print "Phase 2..."
	# For every addressed node, look at possible ways to remove id again.
	# Find addressed leaf-positions
	# Add frequency counts
	newtrees = []
	for (t1, t2, links) in linked_subtrees2:
		print t1, t2, links
		leafindex1 = dict(frontier_nodes(t1))
		leafindex2 = dict(frontier_nodes(t2))

		indices12 = [(leafindex1[l], leafindex2[l], l) for l in leafindex1.keys()]
		for a in sublists(indices12):
			#print "sublist...", a
			leaves = [str(b[2]) for b in indices12 if not (b in a)]
			newtree1 = t1.copy(True)
			newtree2 = t2.copy(True)
			for (l, r, leaf) in a:
				newtree1[l].node = rmid(str(newtree1[l].node))
				newtree2[r].node = rmid(str(newtree2[r].node))
			newtrees.append((newtree1, newtree2, links,
				product(count(leaf, linked_subtrees) for leaf in leaves)))
			if "@" in newtree1.node:
				newtree1a = newtree1.copy(True)
				newtree2a = newtree2.copy(True)
				newtree1a.node = str(rmid(newtree1.node))
				newtree2a.node = str(rmid(newtree2.node))
				newtrees.append((newtree1a, newtree2a, links,
					product(count(leaf, linked_subtrees) for leaf in leaves)) )
	return newtrees

def leaves_and_frontier_nodes(tree):
	leaves = []
	for child in tree: 
		if isinstance(child, Tree) and len(child) > 0: 
			leaves.extend(leaves_and_frontier_nodes(child)) 
		else: 
			leaves.append(child)
	return leaves

def leaves_and_frontier_nodes1(tree):
	leaves = []
	for child in tree: 
		if isinstance(child, Tree) and child.height() == 2 and not isinstance(child[0], Tree):
			leaves.append(child) #POS tag
		elif isinstance(child, Tree) and len(child) > 0:
			leaves.extend(leaves_and_frontier_nodes1(child))
		else:
			leaves.append(child)
	return leaves

def my_flatten1(tree):
	return Tree(tree.node, leaves_and_frontier_nodes1(tree))
def my_flatten(tree):
	return Tree(tree.node, leaves_and_frontier_nodes(tree))

def count(our_node, linked_subtrees):
	for (a, b) in linked_subtrees:
		if str(a.node) == our_node:
			return product(count(str(c), linked_subtrees) + 1 for
				c in set(x for x,y in frontier_nodes(a)))
				#c in set(x for x,y in dict(frontier_nodes(a)).keys())
	return -1

def frontier_nodes(tree):
	if frontier_node(tree):
		return [(tree.node, ())]
	elif type(tree) == str:
		return []
	else:
		#return list(reduce(chain, (((fnode, ((pos,) + r)) for (fnode, r) in frontier_nodes(stree)) for pos, stree in  enumerate(tree)), ()))
		fnodes = []
		for pos, stree in enumerate(tree):
			#fnodes += [(fnode, ((pos,) + r)) for (fnode, r) in frontier_nodes(stree)]
			fnodes += [(fnode, (pos,) + r) for (fnode, r) in frontier_nodes(stree)]
		return fnodes

#def frontier_nodes(tree):
#	return dict((l, p) for l, p
#		in zip(tree.leaves(), tree.treepositions('leaves')) if '@' in l)

def frontier_node(tree):
	return (isinstance(tree, Tree) and len(tree) == 0)

def product(l):
	return reduce(lambda x, y: x * y, l, 1)

def sublists(l):
	return chain(
		reduce(chain, (combinations(l, a) for a in range(len(l))), () ), (l,))

def rmid(x):
	return x.split("@")[0]

def decorate_with_ids(tree):
	global current_id
	utree = tree.copy(True)
	for a in utree.subtrees():
		if not ("@" in a.node):
			a.node = "%s@%d" % (a.node, current_id)
			current_id += 1
	return utree

def decorate_pair(tree1, tree2):
	global current_id
	utree1 = tree1.copy(True)
	utree2 = tree2.copy(True)
	utree1.node = "%s@%d" % (utree1.node, current_id)
	utree2.node = "%s@%d" % (utree2.node, current_id)
	current_id += 1
	return (utree1, utree2)

def treeify(node):
	if type(node) == Nonterminal:
		return Tree(str(node), [])
	else:
		return node
	
def production_to_tree(production):
	return Tree(str(production.lhs()), [treeify(r) for r in production.rhs()])

def my_subtrees(tree): 
	for (n, child) in zip(range(len(tree)), tree): 
		yield (tree, n, child)
		if isinstance(child, Tree): 
			for subtree in my_subtrees(child): 
				yield subtree

def test():
	tree1 = Tree("(S (NP John) (VP (V bought) (NP (DET a) (N car))))")
	tree2 = Tree("(S (VBZ did) (NP John) (VP (V buy) (NP (DET a) (N car))))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a in t: print a
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print
	gr = grammardict.TransformationDOP()
	gr.add_to_grammar(t2)
	gr.print_grammar()
	a = gr.get_grammar()
	return a

def test2():
	tree1 = Tree("(S (NP mary) (VP walks))")
	tree2 = Tree("(S (VBZ did) (NP mary) (VP walk))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a in t: print a
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print

def forcepos(tree):
	""" make sure all terminals have POS tags; 
	invent one if necessary ("parent_word") """
	result = tree.copy(True)
	for a in tree.treepositions('leaves'):
		if len(tree[a[:-1]]) != 1:
			result[a] = Tree("%s_%s" % (tree[a[:-1]].node, tree[a]), [tree[a]])
	return result

def extendlex(corpus):
	newrules, newlex = FreqDist(), set()
	for a,b in corpus:
		newlex.update(a.leaves())
		newlex.update(b.leaves())
		for x in a.productions():
			if len(x.rhs()) > 0 and '' not in map(str, x.rhs()):
				newrules.inc("%s	%s" % (str(x.lhs()), "\t".join(str(y) for y in x.rhs())))
		for x in b.productions():
			if len(x.rhs()) > 0 and '' not in map(str, x.rhs()):
				newrules.inc("%s	%s" % (str(x.lhs()), "\t".join(str(y) for y in x.rhs())))
		#for x in a.treepositions('leaves'):
		#	newrules.inc("%s	%s" % (a[x[:-1]].node, a[x]))
		#for x in b.treepositions('leaves'):
		#	newrules.inc("%s	%s" % (b[x[:-1]].node, b[x]))
	return newrules.items(), newlex

def runexp():
	corpus = list(zip(map(Tree, open("corpus/trees-interr3.debin.txt")), 
			map(Tree, open("corpus/trees-decl3.txt")))) #[:5]
	print 'corpus:'
	# for a,b in corpus: print "< %s\n %s  >\n\" % (str(a), str(b))

	tdop = TransformationDOP()
	for n, (tree1, tree2) in enumerate(corpus[:10]):
		#tree1.chomsky_normal_form()
		#tree2.chomsky_normal_form()
		print n
		min = minimal_linked_subtrees(tree1[0], tree2[0])
		lin = linked_subtrees_to_probabilistic_rules(min)
		tdop.add_to_grammar(lin)
		min = minimal_linked_subtrees(tree2[0], tree1[0])
		lin = linked_subtrees_to_probabilistic_rules(min)
		tdop.add_to_grammar(lin)
	print "training done"
	parser = ViterbiParser(tdop.get_grammar())
	#rules, lexicon = tdop.get_grammar(bitpar=True)
	#newrules, newlex = extendlex(corpus[10:])
	#rules.extend(newrules)
	#lexicon.extend(newlex)
	#parser2 = BitParChartParser(rules, lexicon, rootsymbol="TOP")
	results = []
	print 'grammar done'
	#for n, a in enumerate(open("corpus/sentences-interr3.txt").read().splitlines()[:10]):
	for n, a in enumerate(open("corpus/sentences-decl3.txt").read().splitlines()[:10]):
		print n, a
		try:
			parsetree = parser.parse(a.split())
		except Exception as e:
			#try:
			#	parsetree = parser2.parse(a.split())
			#	print "bitpar ok" 
			#except Exception as f:
			print "parsing failed"
			print n, e

		print "parsed", parsetree
		if parsetree:
			try:
				result = tdop.get_mlt_deriv(parsetree)
			except Exception as e:
				print "mlt failed"
				result = None
				print n, e
			print "transformed", result
			if result: 
				print "words", " ".join(result.leaves())
				results.append("%s\n" % " ".join(result.leaves()))
			else:
				results.append("\n")
		else:
			results.append("\n")
	print "done"			
	open("results.txt", "w").writelines(results)

def interface():
	corpus = """(S (NP John) (VP (V bought) (NP (DET a) (N car))))
(S (VP (VBZ did)) (NP John) (VP (V buy) (NP (DET a) (N car))))
	(S (NP Mary) (VP (VBZ is) (ADJP (JJ happy))))
	(S (VBZ is) (NP Mary) (ADJP (JJ happy)))
	(S (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBZ is) (VP (VBG walking))))
	(S (VBZ is) (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBG walking)))"""
	corpus = map(Tree, corpus.splitlines())
	for a in corpus: a.chomsky_normal_form()
	corpus = zip(corpus[::2], corpus[1::2])
	print 'corpus:'
	for a,b in corpus: print "< %s, %s  >" % (str(a), str(b))

	tdop = TransformationDOP()
	for tree1, tree2 in corpus:
		m = minimal_linked_subtrees(tree2, tree1)
		l = linked_subtrees_to_probabilistic_rules(m)
		tdop.add_to_grammar(l)
		tdop.add_to_grammar(linked_subtrees_to_probabilistic_rules(
					minimal_linked_subtrees(tree1, tree2)))
	# not yet working, need to transform grammar to cnf first:
	#rules, lexicon = tdop.get_grammar(bitpar=True)
	#parser = BitParChartParser(rules, lexicon, rootsymbol="S")
	parser = ViterbiParser(tdop.get_grammar())
	print 'done'

	#basic REPL
	while True:
		print 'sentence:',
		a=raw_input()
		try:
			parsetree = parser.parse(a.split())
			
			print "source:", parsetree
			transformed = tdop.get_mlt_deriv(parsetree)
			print "transformed:", transformed
			print "words:", " ".join(transformed.leaves())
		except Exception as e:
			print e

if __name__ == '__main__':
	import doctest
	# do doctests, but don't be pedantic about whitespace
	fail, attempted = doctest.testmod(verbose=False,
	optionflags=doctest.NORMALIZE_WHITESPACE | doctest.ELLIPSIS)
	if attempted and not fail:
		print "%d doctests succeeded!" % attempted
	if argv[1] and argv[1] in "runexp interface test test2".split(): eval(argv[1] + '()')
	else: print "run with one of these arguments: runexp interface test test2"
