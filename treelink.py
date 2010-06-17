from bitpar import BitParChartParser
from nltk import Tree, WeightedProduction, WeightedGrammar, \
	InsideChartParser, FreqDist, WordNetLemmatizer, Nonterminal
from itertools import chain, combinations

USE_LEMMATIZATION = True

current_id = 0

class TransformationDOP:
    def __init__(self):
        self.grammardict = {}

    def add_to_grammar(self, mlsts, source="left"):
        # Adds the minimal linked subtrees (mlsts) to the grammar.
        for (lefttree, righttree, links, count) in mlsts:
            if source == "right":
                lefttree, righttree = righttree, lefttree
            flattened_tree = my_flatten(lefttree)
            index = filter(lambda x: len(x.rhs()) > 0,
                           my_flatten(lefttree).productions())[0]
            if index in self.grammardict.keys():
                tree_links_found = False
                for (curtree, curlinks, curcount) in self.grammardict[index]:
                    if curtree == righttree and curlinks == links:
                        tree_links_found = True
                        self.grammardict[index].remove((curtree, curlinks, curcount))
                        self.grammardict[index].append((curtree, curlinks, curcount + count))
                if not tree_links_found:
                    self.grammardict[index].append((righttree, links, count))
            else:
                self.grammardict[index] = [(righttree, links, count)]
        pass

    def print_grammar(self):
        for (key, value) in self.grammardict.items():
            print "Source rule: %s\n\n" % key
            for (tree, links, count) in value:
                print "  Tree: %s\n" % tree
                print "  Links: %s\n" % links
                print "  Count: %s\n\n" % count
            print

    def get_grammar(self, freqfn=max, prob=True, root="S"):
        # Returns a PCFG. (Use freqfn=max for most likely derivation, prob=sum for most likely parse)
        # grammar = []
        #for (key, value) in self.grammardict.items():
        #    grammar.append(WeightedProduction(key.lhs(), key.rhs(), prob=freqfn([count for tree, links, count in value])))
        # return grammar
	grammar = [ WeightedProduction(key.lhs(), key.rhs(), prob=freqfn(count for tree, links, count in value))
        	         for key, value in self.grammardict.items() ]
	if prob:
		fd = FreqDist()
		for key in grammar:
			fd.inc(key.lhs(), count=key.prob())
		#fd = FreqDist((key.lhs(), key.prob()) for key in grammar)
		grammar = [WeightedProduction(key.lhs(), key.rhs(), 
			prob=freqfn(count for tree, links, count in value) / float(fd[key.lhs()]))
        	        for key, value in self.grammardict.items()]
	        return WeightedGrammar(Nonterminal(root), grammar)
	else:
		return grammar


    def get_mlt_deriv(self, tree):
        # Returns the most likely transformation of tree (based on the most likely derivation).
        top_production = tree.productions()[0]

        # Finds the most likely right hand side of top-production
        maxcount = 0
        for (curtree, curlinks, curcount) in self.grammardict[top_production]:
            if curcount > maxcount:
                righttree, links, count = curtree, curlinks, curcount

        new_subtrees = []
        for a in tree:
            if isinstance(a, Tree):
                new_subtrees.append(self.get_mlt_deriv(a))

        # Add new subtrees
	frontiers = frontier_nodes(righttree)
	target = righttree.copy(True)
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
			wnl = WordNetLemmatizer() 
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

	# Decompose linked subtrees into minimal subtrees (so far: these always are
	# PCFG-rules)
	minimal_subtrees = []
	for i in linked_subtrees:
		for j in i.productions():
			if len(j.rhs()) > 0:
				minimal_subtrees.append(
					(production_to_tree(j), production_to_tree(j)))

	for (x, y) in equivalents:
		minimal_subtrees.append((x, y))

	minimal_subtrees.append((tree1, tree2))
	return minimal_subtrees

def linked_subtrees_to_probabilistic_rules(linked_subtrees):
	# Add 'links' between leaf nodes.
	linked_subtrees2 = []
	for (t1, t2) in linked_subtrees:
		l1 = filter(lambda x: (isinstance(x, Tree) and '@' in x.node), leaves_and_frontier_nodes(t1))
		l2 = filter(lambda x: (isinstance(x, Tree) and '@' in x.node), leaves_and_frontier_nodes(t2))
		# Very ugly, but might be needed to guarantee the right outcome...
		a = [(l1.index(x), l2.index(x)) for x in l1]
		a.sort
		a = [x[1] for x in a] 
		linked_subtrees2.append((t1, t2, a))

	# For every addressed node, look at possible ways to remove id again.
	# Find addressed leaf-positions
	# Add frequency counts
	newtrees = []
	for (t1, t2, links) in linked_subtrees2:
		leafindex1 = dict(frontier_nodes(t1))
		leafindex2 = dict(frontier_nodes(t2))

		indices12 = [(leafindex1[l], leafindex2[l], l) for l in leafindex1.keys()]
		for a in sublists(indices12):
			leaves = [str(b[2]) for b in indices12 if not (b in a)]
			newtree1 = t1.copy(True)
			newtree2 = t2.copy(True)
			for (l, r, leaf) in a:
				newtree1[l].node = rmid(str(newtree1[l].node))
				newtree2[r].node = rmid(str(newtree2[r].node))
			newtrees.append(
				(newtree1, newtree2, links,
				product(count(leaf, linked_subtrees) for leaf in leaves)))
			if "@" in newtree1.node:
				newtree1a = newtree1.copy(True)
				newtree2a = newtree2.copy(True)
				newtree1a.node = str(rmid(newtree1.node))
				newtree2a.node = str(rmid(newtree2.node))
				newtrees.append(
					(newtree1a, newtree2a, links,
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

def my_flatten(tree):
	return Tree(tree.node, leaves_and_frontier_nodes(tree))

def count(our_node, linked_subtrees):
	for (a, b) in linked_subtrees:
		if str(a.node) == our_node:
			return product([
				count(str(c), linked_subtrees) + 1 for
				c in dict(frontier_nodes(a)).keys()])
	return -1

def frontier_nodes(tree):
	if frontier_node(tree):
		return [(tree.node, ())]
	elif type(tree) == str:
		return []
	else:
		fnodes = []
		for (stree, pos) in zip(tree, range(len(tree))):
			fnodes += [(fnode, ((pos,) + r)) for (fnode, r) in frontier_nodes(stree)]
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
	tree2 = Tree("(S (NP mary) (VP walks))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a in t: print a
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print

def test3():
	corpus = """(S (NP John) (VP (V bought) (NP (DET a) (N car))))
(S (VBZ did) (NP John) (VP (V buy) (NP (DET a) (N car))))
(S (NP Mary) (VP (VBZ is) (ADJP (JJ happy))))
(S (VBZ is) (NP Mary) (ADJP (JJ happy)))
(S (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBZ is) (VP (VBG walking))))
(S (VBZ is) (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBG walking)))""".splitlines()
	corpus = map(Tree, corpus)
	corpus = zip(corpus[::2], corpus[1::2])
	print 'corpus:', corpus

	tdop = TransformationDOP()
	print 'gr', tdop
	for tree1, tree2 in corpus:
		tdop.add_to_grammar(linked_subtrees_to_probabilistic_rules(
					minimal_linked_subtrees(tree1, tree2)))
	print 'a2gr', tdop.get_grammar()
	parser = InsideChartParser(tdop.get_grammar())
	print 'done'
	parsetree = parser.parse("John bought a car".split())
	print parsetree
	print tdop.get_mlt_deriv(parsetree)

	while True:
		print 'sentence:',
		a=raw_input()
		try:
			parsetree = parser.parse(a.split())
		except:
			parsetree = None
		print "source:", parsetree
		if parsetree:
			print "transformed:", tdop.get_mlt_deriv(parsetree)


test3()

# (Tree('NP@0', ['DET@1', 'N@2']), Tree('NP@0', ['DET@1', 'N@2']))
# (Tree('DET@1', ['a']), Tree('DET@1', ['a']))
# (Tree('N@2', ['car']), Tree('N@2', ['car']))
# (Tree('NP@3', ['John']), Tree('NP@3', ['John']))
# (Tree('VP@5', ['V@4', 'NP@0']), Tree('VP@5', ['V@4', 'NP@0']))
# (Tree('V@4', ['bought']), Tree('V@4', ['buy']))

