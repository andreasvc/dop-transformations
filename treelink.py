from bitpar import BitParChartParser
from memoize import memoize
from nltk import Tree, WeightedProduction, WeightedGrammar,\
	ViterbiParser, FreqDist, WordNetLemmatizer, Nonterminal, ImmutableTree
from itertools import chain, combinations, product, permutations
from operator import mul
from collections import defaultdict
from sys import argv
from heapq import heappush, heappop, nlargest
USE_LEMMATIZATION = True
# number of partial subtree matches to consider:
NUM_PARTIAL = 10
# whether to make sure a substitution is allowed on the target side (otherwise only the source side is checked)
global CHECK_SUBSTITUTION
CHECK_SUBSTITUTION = False
wnl = WordNetLemmatizer() 

current_id = 1
def topdownparse(grammar, sent, root="top"):
	# Roark's Fully-Connected Parsing Algorithm
	# not working yet.
	# Python's heapq is a min-heap, so we do everything with negative numbers.
	def above_threshold(h, C, N): 
		if h[0] < -0.00005: return True
	def LAP(t1, w1): return -1.0
	C, N = [], []
	h = (q, r, t) = (-1, -1, Tree(root, []))
	C.append((q, r, t))
	for i,w in enumerate(sent):
		while above_threshold(h, C, N):
			h = heappop(C)
			for x in (x for x in grammar if x.prob() * -q > 0): # ??
				q1 = q * x.prob() # ??
				t1 = join(t, production_to_tree(x))
				if t1 == None: continue
				if x.rhs()[0] == w:
					w1 = sent[i+1]
					r1 = LAP(t1, w1)
					h1 = (q1, r1, t1)
					heappush(N, h1)
				else:
					w1 = w
					r1 = LAP(t1, w1)
					h1 = (q1, r1, t1)
					heappush(C, h1)
		C = []
		C, N = N, C
	prob, foo, tree = heappop(C)
	return tree, prob

def mytopdownparse(grammar, sent, t=None, depth=1, depthlimit=3):
	# primitive topdown parser
	if t == None: t = Tree("top", [])
	if depth >= depthlimit: raise StopIteration
	substitution_sites = [a.node for a in t.subtrees() if len(a) == 0]
	if substitution_sites:
		leftmost = Nonterminal(substitution_sites[0])
		candidates = [a for a in grammar._lhs_index[leftmost]] 
		# ^^... if sent[0] in grammar._leftcorners[a.lhs()]]
		rec, nonrec = [], []
		for a in candidates:
			if a.lhs() in a.rhs(): rec.append(a)
			else: nonrec.append(a)
		for x in nonrec:
			t1 = join(t, production_to_tree(x))
			if t1.leaves() <> sent[:len(t1.leaves())]: continue
			grammar._lhs_index[leftmost].remove(x)
			grammar._lhs_index[leftmost].append(x)
			for a, p in mytopdownparse(grammar, sent[len(t1.leaves()):], 
				t1, depth): 
				yield a, x.prob() * p
		for x in rec:
			t1 = join(t, production_to_tree(x))
			if t1.leaves() <> sent[:len(t1.leaves())]: continue
			grammar._lhs_index[leftmost].remove(x)
			grammar._lhs_index[leftmost].append(x)
			for a, p in mytopdownparse(grammar, sent[len(t1.leaves()):], 
				t1, depth+1): 
				yield a, x.prob() * p
	elif t.leaves() == sent: yield t, 1
			
def join(a, b):
	for c in a.treepositions():
		# non-terminal node, same label as b, empty node
		if isinstance(a[c], Tree) and a[c].node == b.node and len(a[c]) == 0:
			d = a.copy(True)
			d[c].extend(b)
			return d

class TransformationDOP:
	def __init__(self):
		self.grammardict = defaultdict(FreqDist)
		self.mygrammardict = defaultdict(FreqDist)
		self.fd = FreqDist()
		self.mangled = {}

	def add_to_grammar(self, mlsts, source="left"):
		# Adds the minimal linked subtrees (mlsts) to the grammar.
		print "adding to grammar"
		for (lefttree, righttree, links, count) in mlsts:
			if source == "right":
				lefttree, righttree = righttree, lefttree
			righttree = righttree.freeze()
			links = tuple(links)
			flattened_tree = my_flatten(lefttree)
			index = filter(lambda x: len(x.rhs()) > 0, 
							flattened_tree.productions())[0]
			self.grammardict[index].inc((righttree, links), count)
			self.mygrammardict[lefttree.freeze()].inc((righttree, links), count)
			self.fd.inc(index.lhs(), float(count))

	def sort_grammar(self, withids=False):
		# sort the grammar by fragment size, largest first
		if withids:
			self.mygrammarsorted = sorted((a
						for a in self.mygrammardict.keys()), 
						key=lambda x: len(x.treepositions()), 
						reverse=True)
		else:
			self.mygrammarsorted = sorted(set(undecorate_with_ids(a).freeze() 
						for a in self.mygrammardict.keys()), 
						key=lambda x: len(x.treepositions()), 
						reverse=True)

	def extendlex(self, corpus):
		# collect all preterminals and terminals from a corpus, add them as
		# linked subtrees.
		for a,b in corpus:
			blem = dict((wnl.lemmatize(w, "v"), (w,p)) for w,p in b.pos())
			for word, pos in a.pos():
				lem = wnl.lemmatize(word, "v")
				if wnl.lemmatize(word, "v") in blem:
					right = ImmutableTree(blem[lem][1], [blem[lem][0]])
				else:	right = ImmutableTree(pos, [word])
				left = ImmutableTree(pos, [word])
				x = left.productions()[0]
				self.grammardict[x].inc((right, ()))
				self.mygrammardict[left].inc((right, ()))
				self.fd.inc(x.lhs(), 1.)

	def print_grammar(self):
		for (key, value) in self.grammardict.items():
			print "Source rule: %s\n" % key
			for ((tree, links), count) in value.items():
				print "  Tree: %s" % tree
				print "  Links: %s" % repr(links)
				print "  Count: %d\n" % count
			print

	def get_grammar(self, freqfn=sum, prob=True, bitpar=False, root="S"):
		# Returns a PCFG. (Use freqfn=max for most likely derivation, 
		#	prob=sum for most likely parse)  <-- this can't be correct.
		grammar = [ WeightedProduction(key.lhs(), key.rhs(), 
						prob=freqfn(count for (tree, links), count 
							in value.items())) 
						for key, value in self.grammardict.items() ]
		if prob:
			if bitpar:
				lexicon = list(chain(*((a for a in key.rhs() 
					if not isinstance(a, Nonterminal)) 
					for key in self.grammardict)))
				grammar = []
				for key, value in self.grammardict.items():
					count = freqfn(value.values())
					tmp = forcepos(production_to_tree(key))
					tmp.chomsky_normal_form()
					for a in tmp.productions():
						if len(a.rhs()):
							grammar.append(("%s\t%s" % (str(a.lhs()), 
										"\t".join(map(str, a.rhs()))), count))
				return grammar, lexicon
			else:
				grammar = [WeightedProduction(key.lhs(), key.rhs(), 
					prob=freqfn(value.values()) / self.fd[key.lhs()])
					for key, value in self.grammardict.items()]
				return WeightedGrammar(Nonterminal(root), grammar)
		else:
			return grammar
	
	def get_my_grammar(self, bitpar=False, root="S"):
		grammar = FreqDist()
		lexicon = list(reduce(chain, (tree.leaves() for tree 
									in self.mygrammardict)))
		for key, value in self.mygrammardict.items():
			count = max(value.values())
			tmp = Tree.convert(key)
			if bitpar: forcepos(tmp).chomsky_normal_form()
			for a in tmp.productions():
				if len(a.rhs()):
					if bitpar:
					# fixme: proper goodman frequencies here of course
						grammar.inc("%s\t%s" % (str(a.lhs()), 
								"\t".join(map(str, a.rhs()))), count)
					else:
						grammar.inc(a, count)
		if bitpar:
			return grammar.items(), lexicon
		fd = FreqDist()
		for k,v in grammar.items(): fd.inc(k.lhs(), v)
		return WeightedGrammar(Nonterminal(root), 
				[WeightedProduction(k.lhs(), k.rhs(), 
					prob=v/float(fd.get(k.lhs(),v))) 
					for k,v in grammar.items()])
		
			
	def my_mlt_deriv(self, tree, allowpartial=False):
		# translation using subtrees instead of flattened trees
		def match(tree, candidate):
			# walk through candidate and compare to tree
			for idx in candidate.treepositions():
				try:
					if tree[idx] == candidate[idx]: continue
					if tree[idx].node <> candidate[idx].node: return False
					if len(candidate[idx]) not in (0, len(tree[idx])): 
						return False
				except: return False
			return True
		def similarity(tree, candidate):
			# walk through candidate and compare to tree
			# same node at same index is full points, same node at a different
			# index in the same constituent is half points, weighted by height
			# with higher nodes having more weight.
			sim = 0.0
			h = float(candidate.height())
			links = {}
			for idx in sorted(candidate.treepositions()[1:], key=len):
				try:
					if (isinstance(candidate[idx], str) 
						and tree[idx] == candidate[idx]): 
						sim += 1 #* (candidate[idx].height() / h)
					elif (isinstance(candidate[idx], str)
						and candidate[idx] not in tree.leaves()):
						return 0, {}
					if (candidate[idx].node in 
						[a.node for a in tree[idx[:-1]]]): 
						sim += 0.5 #* (candidate[idx].height() / h)
					if tree[idx].node == candidate[idx].node: 
						sim += 0.5 #* (candidate[idx].height() / h)
					# align all nodes of this type in a greedy fashion
					matches = [n for n, a in enumerate(tree[idx[:-1]]) if a.node == candidate[idx].node]
					competing = [n for n, a in enumerate(candidate[idx[:-1]]) if a.node == candidate[idx].node]
					for n in matches:
						nearest = min(((m - n), m) for m in competing)[1]
						links[idx[:-1] + (nearest,)] = idx[:-1] + (n,)
						competing.remove(nearest)
				except: pass
				# no similarity at level directly under parent => fail
				if len(idx) > 0 and sim == 0: return 0, {}
				# other idea: similarity should be nonzero within each constituent
			a = sim / len(tree.treepositions())
			b = sim / len(candidate.treepositions())
			# harmonic mean
			result = (2 * a * b) / (a + b)
			return result, links

		yielded = False
		matched = False
		for candidate in self.mygrammarsorted:
			if match(tree, candidate):
				matched = True
				for righttree, links in self.mygrammardict[candidate]:
					count = self.mygrammardict[candidate][(righttree, links)]
					lhscount = self.fd.get(Nonterminal(candidate.node), count)
					target = Tree.convert(righttree)
					lfrontiers = list(frontier_nodes(candidate))
					frontiers = list(frontier_nodes(righttree))
					if not lfrontiers:
						#print "no frontiers", target, count, "/", lhscount
						yield target, count / lhscount
						yielded = True
						continue
					#new_subtree_forest = product(*(self.my_mlt_deriv(tree[a[1]]) for a in lfrontiers))
					#new_subtree_forest = list(product(*[list(self.my_mlt_deriv(tree[a[1]])) for a in lfrontiers]))
					new_subtree_forest = []
					for a in lfrontiers:
						new_subtree_forest.append(list(self.my_mlt_deriv(tree[a[1]], allowpartial)))
					new_subtree_forest = list(product(*new_subtree_forest))
					for new_subtrees in new_subtree_forest:
						target = Tree.convert(righttree)
						for (subtree, freq), index in zip(new_subtrees, links):
							idx = frontiers[index][1]
							# check if substitution is on a matching node, 
							if not CHECK_SUBSTITUTION or subtree.node == target[idx].node:
								target[frontiers[index][1]] = subtree
							else:	
							#	print "illegal righttree; expected", target[idx].node, "got", subtree
								break
						else:
							prob = count / lhscount * reduce(mul, (a[1] for a in new_subtrees), 1)
							#print "used", candidate, "=>", righttree
							yield target, prob
							yielded = True
						#if target.node == "top": break # stop deriving after first full derivation
					#else: continue # with other right trees
					#break
				#else: continue # with other candidates (left trees)
				#break
		if not yielded and tree.node not in ("top", "s", "sq", "vp"):
			#found nothing, do smoothing
			#print "smoothing for", tree
			yield tree, 1 / self.fd.get(Nonterminal(tree.node))
		elif (not matched) and allowpartial and len(tree):
			# do partial match here
			#score, candidate = sorted([(similarity(tree, a), a) for a in self.mygrammardict if a.node == tree.node])[-1]
			partial = sorted([(similarity(tree, a), a) for a in self.mygrammarsorted if a.node == tree.node], reverse=True)[:NUM_PARTIAL]
			#print "partial matches for", tree
			#for s,p in partial: print s, p
			for (score, links), candidate in partial:
				if score == 0: break
				if any(a not in tree.leaves() for a in candidate.leaves()):
					#print "spurious match", score, links, candidate
					continue

				#print "partial match", score, candidate
				# now rewrite candidate with subtrees from our tree to be translated
				newtree = Tree.convert(candidate)
				covered, notcovered = [], []
				frontiers = frontier_nodes(newtree)
				frontiers.sort(key=lambda x: len(x[1]))
				fnodes = [a[0] for a in frontiers]
				nnodes = [newtree[a].node for a in newtree.treepositions() if isinstance(newtree[a], Tree)]
				# get nodes and indices of current tree that are frontier nodes in the new tree or that don't exist there
				# sort by length of index, so that nodes are sorted by level (highest nodes first)
				# actually we should calculate a proper tree alignment and link each of the nodes
				indices = [a for a in tree.treepositions() if isinstance(tree[a], Tree) 
						and (tree[a].node in fnodes or tree[a].node not in nnodes)]
				indices.sort(key=len)
				nodes = [tree[a].node for a in indices]
				for node, idx in frontiers:
					if idx in links:
						oldidx = links[idx]
						del links[idx]
						newtree[idx] = tree[oldidx]
						# remove the node we just inserted and all of its children, and its parent
						indices = [a for a in indices if a[:len(oldidx)] <> oldidx and a <> oldidx[:-1]]
						nodes = [tree[a].node for a in indices]
						covered.append(node)
				if not covered: continue
				# leftovers not part of our match (recover normal order again):
				notcovered = [a for a in tree.treepositions() if a in indices]
				# veto any partial match if it does not contain a match for the main verb in the original tree (if any)
				verbheads = "md vbz vbp vbd vb".split()
				if any(a in nodes for a in verbheads) and not any(a in covered for a in verbheads): continue
				#print "notcovered", notcovered, "newtree", newtree
				for deriv,prob in self.my_mlt_deriv(newtree, allowpartial):
					if deriv.leaves() == []: continue
					#print "deriv", deriv
					result = munge(deriv, tree, indices)
					self.mangled[(deriv.freeze(), tree.freeze(), tuple(indices))] = result
					#print "munged", result
					yield result, prob * score #1 / self.fd[Nonterminal(tree.node)]
				#	break
		#elif not yielded: print "no cigar", tree

	def get_mlt_deriv_multi(self, tree, smoothing=False, verbose=False):
		global CHECK_SUBSTITUTION
		# Iterator over translations of tree
		top_production = tree.productions()[0]
		if top_production in self.grammardict:
			candidates = self.grammardict[top_production].items()
		elif smoothing:
			if verbose: print "not found", top_production
			candidates = [((production_to_tree(top_production), range(len([a for a in tree if isinstance(a, Tree)]))), 1)]
		else: 
			if verbose: print "not found", top_production
			raise StopIteration
		lhscount = self.fd.get(top_production.lhs(), 1)
		new_subtree_forest = list(product(*(self.get_mlt_deriv_multi(a, smoothing, verbose) for a in tree if isinstance(a, Tree))))

		# Add new subtrees
		for (righttree, links), count in candidates:
			#if verbose: print "using", righttree, "for", tree
			prob = count / lhscount
			frontiers = frontier_nodes(righttree)
			for new_subtrees in new_subtree_forest:
				target = Tree.convert(righttree)
				for n, index in enumerate(links):
					# check if substitution is on a matching node, 
					match = (new_subtrees[n][0].node == target[frontiers[index][1]].node)
					if not CHECK_SUBSTITUTION or match:
						target[frontiers[index][1]] = new_subtrees[n][0]
						#if verbose: print "substituted", new_subtrees[n][0]
					else:
						if verbose: print new_subtrees[n][0], "does not fit with", target, "source", tree
						break
					if not match: prob *= 0.01	#penalty for incorrect label
				else:
					prob *= reduce(mul, (a[1] for a in new_subtrees), 1)
					yield target, prob
				
	def get_mlt_deriv(self, tree, smoothing=False):
		# Returns the most likely transformation of tree (based on the most likely derivation).
		top_production = tree.productions()[0]

		# Finds the most likely right hand side of top-production
		"""count = 0
		for (curtree, curlinks), curcount in self.grammardict[top_production].items():
			if curcount > count:
				righttree, links, count = curtree, curlinks, curcount"""
		if top_production in self.grammardict:
			#righttree, links = self.grammardict[top_production].max()
			candidates = self.grammardict[top_production].items()
		elif smoothing and len(top_production.rhs()) == 1 and not isinstance(top_production.rhs()[0], Nonterminal):
			# assume words are the same
			#righttree, links = tree, []
			#print "lex not found", top_production
			candidates = [((tree, []), 1)]
		elif smoothing:
			#print "not found", top_production
			candidates = [((production_to_tree(top_production), range(len([a for a in tree if isinstance(a, Tree)]))), 1)]
		else: 
			#print "not found", top_production
			raise ValueError
		lhscount = self.fd.get(top_production.lhs(), 1)

		new_subtrees = [self.get_mlt_deriv(a, smoothing) for a in tree if isinstance(a, Tree)]

		# Add new subtrees
		for (righttree, links), count in candidates:
			frontiers = list(frontier_nodes(righttree))
			target = Tree.convert(righttree)
			for n, index in enumerate(links):
				#print index, n, target[frontiers[index][1]], '/', new_subtrees[n]
				target[frontiers[index][1]] = new_subtrees[n][0]
			prob = count / lhscount * reduce(mul, (a[1] for a in new_subtrees), 1)
			return target, prob

def minimal_linked_subtrees(tree1, tree2, decorate=True):
	# Takes out shared subtrees from tree1 and tree2, until nothing is left.
	# Then decomposes the shared subtrees into rules linked to themselves.
	# Then links the remaining (unmatchable) part of tree1 to tree2.
	def ideq(tree1, tree2):
		# test if tree1 and tree2 are equal, but only compare IDs if 
		# nodes have them, so that lemmatized subtrees are recognized as equivalent.
		if len(tree1) == len(tree2):
			if isinstance(tree1, Tree) and isinstance(tree2, Tree):
				if tree1.node.split("@")[-1] == tree2.node.split("@")[-1]:
					return "@" in tree1.node or all(ideq(a,b) for a,b in zip(tree1, tree2))
				else: return False
			else: return tree1 == tree2
		else: return False
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
				#if i == j and isinstance(i, Tree):
				if isinstance(i, Tree) and ideq(i, j):
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
						if isinstance(j, Tree) and	len(j) == 1 and type(j[0]) == str:
							# verbs are handled by the wordnet lemmatizer,
							# handle contractions as special cases.
							if ((((i.node[0] == 'v' and j.node[0] == 'v') or
								(i.node == 'md' and j.node == 'md'))
							and (wnl.lemmatize(i[0], 'v') == wnl.lemmatize(j[0], 'v')
							or (i[0] in ("is", "'s") and j[0] in ("is", "'s") and i[0] <> j[0])))
							or (i[0] in ("not", "n't") and j[0] in ("not", "n't") and i[0] <> j[0])):
								# if word is the same it's probably a tagging error:
								if i[0] == j[0]: 
									pass
									# this leads to overgeneralization
									#i.node = j.node
									#print "corrected tag", j.node, "=>", i.node
								else: print "lemmatized", i[0], "<=>", j[0]
								lemmatized_equivalents = (i, j, parent1, num1, parent2, num2)
							# also do any <=> some

		# Remove the shared subtree from the tree...
		if max_shared_subtree:
			(tree, parent1, num1, parent2, num2) = max_shared_subtree
			# Decorate tree with ids.
			if decorate: tree = decorate_with_ids(tree)
			parent1[num1] = Tree(tree.node, []) # tree.node
			parent2[num2] = Tree(tree.node, []) # tree.node
		elif lemmatized_equivalents:
			(i, j, parent1, num1, parent2, num2) = lemmatized_equivalents
			i, j = decorate_pair(i, j)
			parent1[num1] = Tree(i.node, [])
			parent2[num2] = Tree(j.node, [])
		
		if lemmatized_equivalents:
			equivalents.append((i, j))
		elif max_shared_subtree == None:
			shared_subtrees = False
		else:
			linked_subtrees.append(tree)
	#print "Phase -1"
	# Decompose linked subtrees into minimal subtrees (so far: these always are
	# PCFG-rules)
	minimal_subtrees = []
	for i in linked_subtrees:
		for j in i.productions():
			if len(j.rhs()) > 0:
				minimal_subtrees.append(
					(production_to_tree(j), production_to_tree(j)))
	#print "Phase 0"
	#for (x, y) in equivalents:
	#	minimal_subtrees.append((x, y))
	minimal_subtrees.extend(equivalents)

	minimal_subtrees.append((tree1, tree2))
	return minimal_subtrees

def linked_subtrees_to_probabilistic_rules(linked_subtrees, limit_subtrees=1000):
	def myindex(l, x):
		# only match ID, not label
		for n, a in enumerate(l):
			if x in a.node: return n
		raise ValueError("myindex(x): x not in list")
	# Add 'links' between leaf nodes.
	print "Phase 1..."
	linked_subtrees2 = []
	for t1, t2 in linked_subtrees:
		l1 = filter(lambda x: (isinstance(x, Tree) and '@' in x.node), leaves_and_frontier_nodes(t1))
		l2 = filter(lambda x: (isinstance(x, Tree) and '@' in x.node), leaves_and_frontier_nodes(t2))
		# Very ugly, but might be needed to guarantee the right outcome...
		a = [(l1.index(x), myindex(l2, x.node.split("@")[1])) for x in l1]
		# a.sort()	# ???!?
		a = [x[1] for x in a] 
		linked_subtrees2.append((t1, t2, a))
		#t1.freeze()
		#t2.freeze()
	print "Phase 2..."
	# For every addressed node, look at possible ways to remove id again.
	# Find addressed leaf-positions
	# Add frequency counts
	newtrees = []
	for (t1, t2, links) in linked_subtrees2:
		print t1, t2, links
		leafindex1 = dict(frontier_nodes(t1))
		leafindex2 = dict((a.split("@")[-1], b) for a,b in frontier_nodes(t2))
		# note: a.split("@")[-1] either gives the ID if there is one, or returns the whole string (in case of a leaf)
		indices12 = [(leafindex1[l], leafindex2[l.split("@")[-1]], l) for l in leafindex1.keys() if l.split("@")[-1] in leafindex2]
		for n, a in enumerate(sublists(indices12)):
			if limit_subtrees and n > limit_subtrees: break
			#print "sublist...", a
			leaves = [str(b[2]) for b in indices12 if b not in a]
			newtree1 = t1.copy(True)
			newtree2 = t2.copy(True)
			for (l, r, leaf) in a:
				newtree1[l].node = rmid(newtree1[l].node)
				newtree2[r].node = rmid(newtree2[r].node)
			newtrees.append((newtree1, newtree2, links,
				reduce(mul, (count(leaf, linked_subtrees) for leaf in leaves), 1)))
			if "@" in newtree1.node:
				newtree1a = newtree1.copy(True)
				newtree2a = newtree2.copy(True)
				newtree1a.node = rmid(newtree1.node)
				newtree2a.node = rmid(newtree2.node)
				newtrees.append((newtree1a, newtree2a, links,
					reduce(mul, (count(leaf, linked_subtrees) for leaf in leaves), 1)) )
	return newtrees
		
def munge(deriv, tree, notcovered):
	# deriv is a translation using a partial match, tree is the original tree,
	# notcovered is a list of indices from tree that were not part of the partial match
	# reinsert all constituents from the original tree that were not present in the partial match
	# the challenge is to find the right constituent and index to insert at
	deriv = Tree.convert(deriv)
	# clean up derivation, remove any parts without yield
	tp = deriv.treepositions()
	while tp:
		idx = tp.pop(0)
		if isinstance(deriv[idx], Tree) and deriv[idx].leaves() == []:
			del deriv[idx]
			tp = deriv.treepositions()
	while notcovered:
		nc = notcovered[0]
		# skip frontier nodes or terminals
		indices = [a for a in deriv.treepositions() if isinstance(deriv[a], Tree) and deriv[a]]
		indices.sort(key=len)
		nodes = [deriv[a].node for a in indices]
		# linked nodes would be better
		# try to find its former parent
		idx = None
		parent = tree[nc[:-1]].node
		if len(nc) == 2 and parent == "s": parent = "sq"
		elif len(nc) == 2 and parent == "sq": parent = "s"
		if parent in nodes and len(nc) - 1 == len(indices[nodes.index(parent)]):
			idx = indices[nodes.index(parent)]
		elif any(x.node in nodes for x in tree[nc[:-1]]):
			# put it in a constituent that has a sibling of this node
			siblings = [y.node for y in tree[nc[:-1]]]
			tmp = FreqDist(x[:-1] for x in indices if deriv[x].node in siblings)
			idx = [a for a in tmp if len(a) <= len(nc)]
			if idx: idx = idx.pop()
		if idx == None:
			# try to append it to parent. 
			# otherwise, attach to root
			for n in range(1, len(nc)):
				parent = tree[nc[:-n]].node
				if len(nc[:-n]) == 1 and parent == "s": parent = "sq"
				elif len(nc[:-n]) == 1 and parent == "sq": parent = "s"
				if parent in nodes and len(nc) - n == len(indices[nodes.index(parent)]):
					idx = indices[nodes.index(parent)]
					break
				else: idx = ()
		if idx: deriv[idx] = Tree.convert(guessorder(deriv[idx], tree, nc))
		else: deriv = Tree.convert(guessorder(deriv[idx], tree, nc))
		# remove this node and all of its children as we've covered them now
		notcovered = [x for x in notcovered if x[:len(nc)] <> nc]
	return deriv
def guessorder(deriv, tree, notcovered):
	def partition(list, middle):
		for n in range(len(list)):
			if list[n:n+len(middle)] == middle:
				return list[:n], list[n+len(middle):]
		raise ValueError("middle not in list")
	#guess proper order
	left, right = partition([a for a,b in tree.pos()], [a for a,b in tree[notcovered].pos()])
	leftp, rightp = partition([b for a,b in tree.pos()], [b for a,b in tree[notcovered].pos()])
	positions = []
	for n in range(len(deriv)+1):
		dleft = chain(*(x.pos() for x in deriv[:n] if isinstance(x, Tree)))
		dright = chain(*(x.pos() for x in deriv[n:] if isinstance(x, Tree)))
		# match on words, backoff to POS tags only if word is not found
		positions.append((sum(1 for a,b in dleft if a in left or (a not in right and b in leftp)) 
				+ sum(1 for a,b in dright if a in right or (a not in left and b in rightp)),
				#min(notcovered[-1], n) - max(notcovered[-1], n),
				n))
		# how to break a tie? idea: generate both..
		# currently: pick index closest to original index

	deriv.insert(max(positions, #key=lambda x: x[0]
		)[-1], tree[notcovered])
	#print tree[notcovered].node, "=>", deriv.node, "positions", positions
	return deriv

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

#@memoize
def count(our_node, linked_subtrees):
	for a, b in linked_subtrees:
		if a.node == our_node:
			return reduce(mul, (count(c, linked_subtrees) + 1 for
				c in set(x for x,y in frontier_nodes(a))), 1)
	return -1

def frontier_nodes(tree):
	if frontier_node(tree):
		return [(tree.node, ())]
	elif type(tree) == str:
		return []
	else:
		#return reduce(chain, ([(fnode, (pos,) + r) for (fnode, r) in frontier_nodes(stree)] for pos, stree in enumerate(tree)))
		fnodes = []
		for pos, stree in enumerate(tree):
			#fnodes += [(fnode, ((pos,) + r)) for (fnode, r) in frontier_nodes(stree)]
			fnodes += [(fnode, (pos,) + r) for (fnode, r) in frontier_nodes(stree)]
		return fnodes

#def frontier_nodes(tree):
#	return dict((l, p) for l, p
#		in zip(tree.leaves(), tree.treepositions('leaves')) if '@' in l)

def frontier_node(tree):
	return isinstance(tree, Tree) and len(tree) == 0

def comb(n):
	result = 0
	for x in range(1, n+1):
		result += reduce(mul, range(1, n+1), 1) / (reduce(mul, range(1, x+1), 1) * reduce(mul, range(1, n-x+1), 1))
	return result

def sublists(l):
	# ordered from big to small:
	return chain( ((),), reduce(chain, (combinations(l, a) for a in range(len(l), 0, -1)), ()))
	# ordered from small to big:
	#return reduce(chain, (combinations(l, a) for a in range(len(l) + 1)))

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

def undecorate_with_ids(tree):
	tree = Tree.convert(tree)
	for a in tree.subtrees(filter=lambda x: '@' in x.node):
		a.node = a.node[:a.node.index("@")]
	return tree

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
	for n, child in enumerate(tree): 
		yield tree, n, child
		if isinstance(child, Tree): 
			for subtree in my_subtrees(child): 
				yield subtree

def test():
	tree1 = Tree("(S (NP John) (VP (V bought) (NP (DET a) (N car))))")
	tree2 = Tree("(S (VBZ did) (NP John) (VP (V buy) (NP (DET a) (N car))))")
	t = minimal_linked_subtrees(tree1, tree2)
	for a,b in t: print a,b
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print
	print
	for b in t2:
		for c in b: print c
		print
	gr = TransformationDOP()
	gr.add_to_grammar(t2)
	gr.print_grammar()
	a = gr.get_grammar()
	return a

def test2():
	tree1 = Tree("(TOP (SQ (VBD Did) (NP (PRP I)) (VP (VB buy) (NP (PRP it))) (. ?)))")
	tree2 = Tree("(TOP (S (NP (PRP I)) (VP (VBD bought) (NP (PRP it))) (. .)))")
	t = minimal_linked_subtrees(tree1, tree2)
	print "\nminimal linked subtrees"
	for a,b in t: print a,b
	print "end\n"
	t2 = linked_subtrees_to_probabilistic_rules(t)
	print "\nlinked subtrees to probabilistic rules"
	for b in t2:
		for c in b: print c
		print
	tdop = TransformationDOP()
	tdop.add_to_grammar(t2)
	tdop.sort_grammar()
	print "DOT grammar"
	tdop.print_grammar()
	tree = Tree("(TOP Did (NP (NNP Mr.) (NNP Freeman)) (VP (VB have) (NP (NP (VB notice)) (PP (IN of) (NP (DT this))))) ?)")
	tree1 = Tree("(TOP (SQ (VBD Did) (NP (NNP Mr.) (NNP Freeman)) (VP (VB have) (NP (NP (VB notice)) (PP (IN of) (NP (DT this))))) (. ?)))")
	tdop.extendlex([(tree1, tree1)])
	parser = ViterbiParser(tdop.get_grammar(root="TOP"))
	print "1"
	t,p = tdop.get_mlt_deriv(tree, smoothing=True)
	print parser.grammar()
	print p, t
	try:
		t,p = tdop.get_mlt_deriv(parser.parse("Did Mr. Freeman have notice of this ?".split()), smoothing=True)
		print p, t
	except Exception as e:
		print e
	print "2"
	tree = Tree("(TOP (SQ (VBD Did) (NP (NNP Mr.) (NNP Freeman)) (VP (VB have) (NP (NP (VB notice)) (PP (IN of) (NP (DT this))))) (. ?)))")
	for t,p in sorted(list(tdop.my_mlt_deriv(tree1)), key=lambda x: x[1]):
		print p, t
	parser = ViterbiParser(tdop.get_my_grammar(root="TOP"))
	print parser.grammar()
	try:
		tree1 = parser.parse("Did Mr. Freeman have notice of this ?".split())
		for t,p in sorted(list(tdop.my_mlt_deriv(tree1)), key=lambda x: x[1]):
			print p, t
	except Exception as e:
		print e
	

def forcepos(tree):
	""" make sure all terminals have POS tags; 
	invent one if necessary ("parent_word") """
	result = tree.copy(True)
	for a in tree.treepositions('leaves'):
		if len(tree[a[:-1]]) != 1:
			result[a] = Tree("%s_word" % (tree[a[:-1]].node), [tree[a]])
	return result

def removeforcepos(tree):
	""" removed forced POS tags of the form "parent_word" """
	result = tree.copy(True)
	for a in tree.treepositions('leaves'):
		if "_" in tree[a[:-1]].node:
			result[a[:-1]] = tree[a]
	return result

def interface():
	corpus = """(S (NP John) (VP (V bought) (NP (DT a) (N car))))
	(S (VP (VBZ did)) (NP John) (VP (V buy) (NP (DT a) (N car))))
	(S (NP Mary) (VP (VBZ is) (ADJP (JJ happy))))
	(S (VBZ is) (NP Mary) (ADJP (JJ happy)))
	(S (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBZ is) (VP (VBG walking))))
	(S (VBZ is) (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBG walking)))"""
	#(S (NP (NP (NP (DT The) (JJ stock-market) (NNS tremors)) (PP (IN of) (NP (NNP Friday)))) (, ,) (NP (NNP Oct.) (CD 13)) (, ,)) (VP (VP (VBD presaged) (NP (JJR larger) (NN fragility))) (, ,) (NP (ADJP (RB far) (JJR greater)) (NNS upheavals))) (. .))
	#(S (VBD Did) (NP (NP (DT the) (JJ stock-market) (NNS tremors)) (PP (IN of) (NP (NP (NNP Friday)) (, ,) (NP (NNP Oct.) (CD 13)) (, ,)))) (VP (VB presage) (NP (NP (JJR larger) (NN fragility)) (, ,) (NP (ADJP (RB far) (JJR greater)) (NNS upheavals)))) (. ?))
	corpus = """(S (NP John) (VP (V walks)))
	(S (NP John) (VP (V loopt)))
	(S (NP Mary) (VP (VBZ is) (ADJP (JJ happy))))
	(S (NP Marie) (VP (VBZ is) (ADJP (JJ blij))))
	(S (NP (NP (DT the) (NN man)) (SBAR (WHNP (WP who)) (S (VP (VBZ is) (VP (VBG talking)))))) (VP (VBZ is) (VP (VBG walking))))
	(S (NP (NP (DT de) (NN man)) (SBAR (WHNP (WP die)) (S (PP (IN aan) (NP (DT het) (NN praten))) (VBZ is)))) (VP (VBZ is) (PP (IN aan) (NP (DT het) (NN lopen)))))"""
	corpus = map(Tree, corpus.lower().splitlines())
	corpus = zip(corpus[::2], corpus[1::2])
	print 'corpus:'
	for a,b in corpus: print "< %s, %s  >" % (str(a), str(b))
	
	tdop = TransformationDOP()
	for tree1, tree2 in corpus:
		m = minimal_linked_subtrees(tree2, tree1)
		l = linked_subtrees_to_probabilistic_rules(m)
		tdop.add_to_grammar(l)
		tdop.add_to_grammar(linked_subtrees_to_probabilistic_rules(minimal_linked_subtrees(tree1, tree2)))
	tdop.sort_grammar()
	parser = ViterbiParser(tdop.get_grammar(root="s"))
	grammar = tdop.get_my_grammar(root="s")
	myparser = ViterbiParser(grammar)
	print 'done'
	#basic REPL
	while True:
		print 'sentence:',
		a=raw_input()
		parsetree = None
		myparsetree = None
		#tree, prob = topdownparse(grammar._productions, a.split(), root="s")
		#for n, result in enumerate(mytopdownparse(grammar, a.split(), t=Tree("s",[]))):
		#	if n > 3: break
		#	print "top down", result[0], result[1]
		try:
			parsetree = parser.parse(a.split())
			print "viterbi1:", parsetree
		except Exception as e:
			print e
		try:
			myparsetree = myparser.parse(a.split())
			print "viterbi2:", myparsetree
		except Exception as e:
			print e
		try:
			transformed, prob = tdop.get_mlt_deriv(parsetree, smoothing=False)
			print "transformed1 (prob=%s): %s" % (repr(prob), transformed)
			print "words:", " ".join(transformed.leaves())
		except Exception as e:
			print e
		if myparsetree in (None, []): continue
		for transformed, prob in list(tdop.my_mlt_deriv(myparsetree)):
			print "transformed2 (prob=%s): %s" % (repr(prob), transformed)
			print "words:", " ".join(transformed.leaves())

def run(tdop, sentsortrees, gold, resultsfile, trees=False, my=False):
	if not trees:
		#parser = ViterbiParser(tdop.get_grammar(root="top"))
		if my:
			rules, lexicon = tdop.get_my_grammar(bitpar=True)
		else:
			rules, lexicon = tdop.get_grammar(bitpar=True, freqfn=sum)
		parser = BitParChartParser(rules, lexicon, cleanup=True, rootsymbol="top", unknownwords="unknownwords", n=1000)
		print 'grammar done'
	results = []
	resultfds = []
	noparse = 0
	for n, a in enumerate(sentsortrees):
		if trees:
			print n, "source:", " ".join(a.leaves())
			parsetrees = {a.freeze() : 1}
		else:
			print n, "source:", a
			try:
				parsetrees1 = list(parser.nbest_parse(a.split()))
			except Exception as e:
				parsetrees1 = []
				print n, "parsing failed", e
			parsetrees = FreqDist()
			for b in parsetrees1: 
				b.un_chomsky_normal_form()
				parsetrees.inc(ImmutableTree.convert(removeforcepos(b)), count=b.prob())
			print "parsetrees:", len(parsetrees)
			if len(parsetrees) == 0: noparse += 1
		resultfd = FreqDist()
		t = 0
		for b in parsetrees:
			if my:
				for nn, (result, prob) in enumerate(tdop.my_mlt_deriv(b)):
					resultfd.inc(" ".join(result.leaves()), count=parsetrees[b] * prob)
					t += 1
					if nn > 1000: break
				#if resultfd: break # skip other parse trees
				if False: pass
				else:
					print "trying partial"
					for nn, (result, prob) in enumerate(tdop.my_mlt_deriv(b, allowpartial=True)):
						t += 1
						resultfd.inc(" ".join(result.leaves()), count=parsetrees[b] * prob)
						if nn > 1000: break
					else: continue # try another parse tree
			for nn, (result, prob) in enumerate(tdop.get_mlt_deriv_multi(b, smoothing=True, verbose=False)):
				if result: resultfd.inc(undecorate_with_ids(result).freeze(), count=parsetrees[b] * prob or 1e-100)
				t += 1
				if nn > 1000: break
		if not trees and not resultfd and parsetrees:
			for nn, (result, prob) in enumerate(tdop.get_mlt_deriv_multi(undecorate_with_ids(parsetrees.keys()[0]), smoothing=False, verbose=False)):
				if result: resultfd.inc(undecorate_with_ids(result).freeze(), count=parsetrees[b] * prob or 1e-100)
				t += 1
				if nn > 1000: break
		print "transformations: ", t
		if not trees:
			resultfd = FreqDist(dict((" ".join(x.leaves()), y) for x,y in resultfd.items()))
		if parsetrees and resultfd:
			results.append("\n".join("%d. [p=%s] %s" % (n, repr(prob), words) for words, prob in resultfd.items()) + "\n")
			print results[-1]
		else:
			results.append("\n")
			#if parsetrees.keys(): print "not transformed:", parsetrees.keys()[0]
		resultfds.append(resultfd)
	if not trees: del parser
	print "done"
	from nltk import edit_distance
	from nltk.metrics import f_measure, precision, recall
	def lem(sent):
		def f(a):
			if a == "n't": return "not"
			if a == "'s": return "is"
			return a
		if sent: return tuple([f(wnl.lemmatize(a, "v")) for a in sent])
		else: return sent
	lgold = [lem(a.split()) for a in gold]
	a,b = 0,0
	dist = []
	dist1 = []
	exact = []
	for n, (fd, sent) in enumerate(zip(resultfds, lgold)):
		if fd.max() and lem(fd.max().split()) == sent: 
			a += 1
			exact.append(n)
		if sent in (lem(x.split()) for x in fd.keys()): b += 1
		if fd: 
			dist.append(min(edit_distance(sent, lem(x.split())) for x in fd))
			dist1.append(edit_distance(sent, lem(fd.max().split())))
		else: 
			dist.append(len(sent))
			dist1.append(len(sent))
	stats = (
	"exact match ranked first: %d of %d => %d %%\n" 
	"exact match of any rank:  %d of %d => %d %%\n" 
	"f-measure: %s\n" 
	"precision: %s\n" 
	"recall: %s\n" 
	"average edit distance (of best matches): %f\n" 
	"sentences with edit distance < 1: %d\n"
	"distances of first matches: %s\n"
	"distances of best matches:  %s\n"
	"indices of exact matches: %s\n" % (
			a, len(gold), float(a) / len(gold) * 100, 
			b, len(gold), float(b) / len(gold) * 100, 
			repr(f_measure(set(lgold), set(lem(x.max().split()) for x in resultfds if x))), 
			repr(precision(set(lgold), set(lem(x.max().split()) for x in resultfds if x))),
			repr(recall(set(lgold), set(lem(x.max().split()) for x in resultfds if x))), 
			sum(dist) / float(len(dist)), 
			len([x for x in dist1 if x <= 1]), 
			repr(dist1), repr(dist), repr(exact)))
	if not trees:
		stats += "sentences with no parse: %d\n" % noparse
	stats += "sentences with no transformation: %d\n" % len([x for x in resultfds if not x])
	print stats
	results.append(stats)
	open(resultsfile, "w").writelines(results)
	return a, b #len([a for a in dist1 if a <= 1])

def runexp():
	import cPickle
	global CHECK_SUBSTITUTION
	sentsinter = open("corpus/sentences-interr3.txt").read().lower().splitlines()
	sentsdecl = open("corpus/sentences-decl3.txt").read().lower().splitlines()
	treesinter = map(lambda x: Tree(x.lower()), open("corpus/trees-interr3.txt"))
	treesdecl = map(lambda x: Tree(x.lower()), open("corpus/trees-decl3.txt"))
	newsentsinter = open("corpus/sentences-interr1.txt").read().lower().splitlines()
	newsentsdecl = open("corpus/sentences-decl1.txt").read().lower().splitlines()
	newtreesdecl = map(lambda x: Tree(x.lower()), open("corpus/trees-decl1.txt"))
	newtreesinter = map(lambda x: Tree(x.lower()), open("corpus/trees-interr1.txt"))
	trees_tdop_parsed = map(lambda x: undecorate_with_ids(Tree(x.lower())), open("trees.txt"))

	#corpus = list(zip(treesdecl, treesinter))[:-20]
	# binarization of corpus. initial testing indicates it only lowers scores.
	def remcnfmarks(tree):
		for a in tree.subtrees(filter=lambda x: '|<>' in x.node):
			a.node = a.node.replace('|<>', '')
	def foldlabels(tree):
		for a in tree.subtrees(filter=lambda x: x.height() > 2 and x.node not in "s sq top np vp".split()):
			a.node = "X"
	def mark_be_do(tree):
		for preterminal in tree.subtrees(filter=lambda x: x.height() == 2):
			if preterminal.node in "vb vbz vbd vbp".split():
				if wnl.lemmatize(preterminal[0], "v") == "be":
					preterminal.node += "_be"
				elif wnl.lemmatize(preterminal[0], "v") == "do":
					preterminal.node += "_do"

	corpus = list(zip(newtreesdecl + treesdecl, newtreesinter + treesinter))[:-20]
	#corpus = list(zip(treesdecl, treesinter))
	#corpus = list(zip(newtreesdecl, newtreesinter))
	for a,b in corpus:
		pass
		#foldlabels(a)
		#foldlabels(b)
		a.chomsky_normal_form(factor='left', horzMarkov=0)
		b.chomsky_normal_form(factor='left', horzMarkov=0)
		remcnfmarks(a)
		remcnfmarks(b)
		#mark_be_do(a)
		#mark_be_do(b)
	for a in treesinter:
		pass
		#foldlabels(a)
		a.chomsky_normal_form(factor='left', horzMarkov=0)
		remcnfmarks(a)
		#mark_be_do(a)
	train = True
	mlsts = []
	if train:
		tdop = TransformationDOP()
		for n, (tree1, tree2) in enumerate(corpus):
			print n
			#minl = minimal_linked_subtrees(tree1, tree2)
			#pos = dict(tree2.pos())
			#for w,p in tree1.pos():
			#	if w in pos and pos[w] <> p:
			#		print "%d. (%s %s) <> (%s %s)" % (n, p, w, pos[w], w)
			#		print minl[-1][0], minl[-1][1]
			#mlsts.append((n, minl[-1], (tree1, tree2), str(minl[-1][0]).count("@"), len(list(minl[-1][0].subtrees())) - 3))
			tdop.add_to_grammar(
				linked_subtrees_to_probabilistic_rules(
				minimal_linked_subtrees(tree2, tree1), limit_subtrees=1000))
		mlsts.sort(key=lambda x: x[4] - x[3])
		x = 0
		for a,(b1,c1), (b,c),d,e in mlsts:
			if e - d > 1:
				print "%d. %d / %d = %f" % (a, d, e, d/float(e))
				print b1
				print c1
				x += 1
				#print b
				#print c
		#print sum(x[3] for x in mlsts), "/", sum(x[4] for x in mlsts), "=", sum(x[3] for x in mlsts) / float(sum(x[4] for x in mlsts))
		print x
		#return
		tdop.extendlex(zip(treesinter, treesdecl)[-20:])
		tdop.sort_grammar(withids=False)
		print "training done" 
	else:
		#tdop = cPickle.load(open("tdop.pickle","rb"))
		pass
	s = [sentsinter[-20 + a] for a in (2,4,6,7,11,12,14,16)]
	sd = [sentsdecl[-20 + a] for a in (2,4,6,7,11,12,14,16)]
	
	#run(tdop, trees_tdop_parsed, "results0.txt", getpos=zip(treesinter, treesdecl)[-20:], trees=True)
	#run(tdop, sentsdecl[-20:], sentsinter[-20:], "results1.txt")
	#run(tdop, s, sd, "results1.txt")
	print "CHECK_SUBSTITUTION", CHECK_SUBSTITUTION
	run(tdop, sentsinter[-20:], sentsdecl[-20:], "results1.txt")

	CHECK_SUBSTITUTION = True
	print "CHECK_SUBSTITUTION", CHECK_SUBSTITUTION
	run(tdop, sentsinter[-20:], sentsdecl[-20:], "results1.txt")

	#run(tdop, treesinter[-20:], sentsdecl[-20:], "results2.txt", trees=True, my=True)
	#run(tdop, treesdecl[-20:], sentsinter[-20:], "results2.txt", trees=True, my=True)
	#cPickle.dump(tdop.mangled, open("mangled.pickle","wb"), 1)
	#tdop.sort_grammar(True)
	#run(tdop, sentsinter[-20:], sentsdecl[-20:], "results3.txt", my=True)
	#run(tdop, newtreesdecl, newsentsinter, "results5.txt", trees=True, my=True)
	print "testing done"
	#if train: cPickle.dump(tdop, open("tdop.pickle","wb"), 1)

def tenfold():
	# first corpus
	sentsinter = open("corpus/sentences-interr3.txt").read().lower().splitlines()
	sentsdecl = open("corpus/sentences-decl3.txt").read().lower().splitlines()
	treesinter = map(lambda x: Tree(x.lower()), open("corpus/trees-interr3.txt"))
	treesdecl = map(lambda x: Tree(x.lower()), open("corpus/trees-decl3.txt"))
	# second corpus
	sentsinter += open("corpus/sentences-interr1.txt").read().lower().splitlines()
	sentsdecl += open("corpus/sentences-decl1.txt").read().lower().splitlines()
	treesdecl += map(lambda x: Tree(x.lower()), open("corpus/trees-decl1.txt"))
	treesinter += map(lambda x: Tree(x.lower()), open("corpus/trees-interr1.txt"))
	from random import sample
	matchesi1, matchesd1 = [], []
	matchesi2, matchesd2 = [], []
	def remcnfmarks(tree):
		for a in tree.subtrees(filter=lambda x: '|<>' in x.node):
			a.node = a.node.replace('|<>', '')
	def foldlabels(tree):
		for a in tree.subtrees(filter=lambda x: x.height() > 2 and x.node not in "s sq top".split()):
			a.node = "X"
	for a in treesinter:
		#a.chomsky_normal_form(factor='left', horzMarkov=0)
		#remcnfmarks(a)
		#foldlabels(a)
		pass
	for a in treesdecl:
		#a.chomsky_normal_form(factor='left', horzMarkov=0)
		#remcnfmarks(a)
		#foldlabels(a)
		pass
	for fold in range(10):
		test = sample(range(len(treesdecl)), 20)
		train = [a for a in range(len(treesdecl)) if a not in test]
		corpus = [(treesdecl[a], treesinter[a]) for a in train]
		tdop = TransformationDOP()
		for n, (tree1, tree2) in enumerate(corpus):
			print n
			min = minimal_linked_subtrees(tree2, tree1)
			lin = linked_subtrees_to_probabilistic_rules(min, limit_subtrees=1000)
			tdop.add_to_grammar(lin)
		tdop.sort_grammar(False)
		tdop.extendlex([(treesinter[a], treesdecl[a]) for a in test])
		print "training done" 
		matchesi1.append(run(tdop, [treesinter[a] for a in test], [sentsdecl[a] for a in test], ("foldd%d.txt" % fold), trees=True, my=True))
		matchesi2.append(run(tdop, [sentsinter[a] for a in test], [sentsdecl[a] for a in test], ("sfoldd%d.txt" % fold), trees=False, my=False))
		tdop = TransformationDOP()
		for n, (tree1, tree2) in enumerate(corpus):
			print n
			min = minimal_linked_subtrees(tree1, tree2)
			lin = linked_subtrees_to_probabilistic_rules(min, limit_subtrees=1000)
			tdop.add_to_grammar(lin)
		tdop.sort_grammar(False)
		tdop.extendlex([(treesdecl[a], treesinter[a]) for a in test])
		print "training done" 
		matchesd1.append(run(tdop, [treesdecl[a] for a in test], [sentsinter[a] for a in test], ("foldi%d.txt" % fold), trees=True, my=True))
		matchesd2.append(run(tdop, [sentsdecl[a] for a in test], [sentsinter[a] for a in test], ("sfoldi%d.txt" % fold), trees=False, my=False))
	matchesi1, matchesi1b = zip(*matchesi1)
	matchesi2, matchesi2b = zip(*matchesi2)
	matchesd1, matchesd1b = zip(*matchesd1)
	matchesd2, matchesd2b = zip(*matchesd2)
	from numpy import std, mean
	print "10 folds, accuracy:"
	print "trees:"
	print "inter => decl:", mean(matchesi1) * 5, "%% (stddev %f) - " % std(matchesi1), 
	print mean(matchesi1b) * 5, "%% (stddev %f)" % std(matchesi1b)
	print "decl => inter:", mean(matchesd1) * 5, "%% (stddev %f) - " % std(matchesd1), 
	print mean(matchesd1b) * 5, "%% (stddev %f)" % std(matchesd1b)
	print
	print "sentences:"
	print "inter => decl:", mean(matchesi2) * 5, "%% (stddev %f) - " % std(matchesi2), 
	print mean(matchesi2b) * 5, "%% (stddev %f)" % std(matchesi2b)
	print "decl => inter:", mean(matchesd2) * 5, "%% (stddev %f) - " % std(matchesd2), 
	print mean(matchesd2b) * 5, "%% (stddev %f)" % std(matchesd2b)

def mungetest():
	import cPickle
	mangled = cPickle.load(open("mangled.pickle","rb"))
	for (deriv, tree, notcovered), result in mangled.items():
		print "deriv", deriv
		print "tree", tree
		print "notcovered", notcovered
		print "former result", result
		print "former leaves:", " ".join(result.leaves())
		newresult = munge(deriv, tree, notcovered)
		if newresult <> result:
			print "current result", newresult
			print "current leaves:", " ".join(newresult.leaves())
		print

if __name__ == '__main__':
	import doctest
	# do doctests, but don't be pedantic about whitespace
	fail, attempted = doctest.testmod(verbose=False,
	optionflags=doctest.NORMALIZE_WHITESPACE | doctest.ELLIPSIS)
	if attempted and not fail:
		print "%d doctests succeeded!" % attempted
	if argv[1] and argv[1] in "runexp tenfold interface mungetest test test2".split(): eval(argv[1] + '()')

