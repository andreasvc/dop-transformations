from nltk import WeightedProduction, Tree, WeightedGrammar
import treelink

class TransformationDOP:
    def __init__(self):
        self.grammardict = {}

    def add_to_grammar(self, mlsts, source="left"):
        # Adds the minimal linked subtrees (mlsts) to the grammar.
        for (lefttree, righttree, links, count) in mlsts:
            if source == "right":
                lefttree, righttree = righttree, lefttree
            flattened_tree = treelink.my_flatten(lefttree)
            index = filter(lambda x: len(x.rhs()) > 0,
                           treelink.my_flatten(lefttree).productions())[0]
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

    def get_grammar(self, freqfn=max):
        # Returns a PCFG. (Use freqfn=max for most likely derivation, prob=sum for most likely parse)
        # grammar = []
        #for (key, value) in self.grammardict.items():
        #    grammar.append(WeightedProduction(key.lhs(), key.rhs(), prob=freqfn([count for tree, links, count in value])))
        # return grammar
        return [ WeightedProduction(key.lhs(), key.rhs(), prob=freqfn(count for tree, links, count in value))
                 for key, value in self.grammardict.items() ]

    def get_mlt_deriv(self, tree):
        # Returns the most likely transformation of tree (based on the most likely derivation).
        top_production = tree.productions()[0]

        # Finds the most likely right hand side of top-production
        maxcount = 0
        for (curtree, curlinks, curcount) in self.grammardict[top_production]:
            if x[2] > maxcount:
                tree, links, count = curtree, curlinks, curcount

        new_subtrees = []
        for a in tree:
            if type(a) == nltk.Tree:
                new_subtrees.append(self.get_mlt_deriv(a))

        # Add new subtrees
        pass
