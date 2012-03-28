import networkx as nx
import matplotlib.pyplot as plt
from threading import *

# of model of storegraph: where a element might be described as a formula, and dependencies on element as directed graph edges
class Storegraph:

    # initialization (with a global)
    def __init__(self, _globals = None):
        
        # the graph of elements and their dependencies
        # by convention:
        # a node successors are nodes which computation depends on it
        # a node predecessors are nodes which values are used in its computation

        self.G = nx.DiGraph()

        # the (python) formula
        self.formulas = dict()

        # the python value
        self.values = dict()

        # the list of callbacks
        # callback:: action -> param -> ()
        # action == "update" -> param == (key, value)
        # action == "delete" -> param == key
        self.callbacks = dict()

        # the mode
        # 0 = lazy: the cell value is to be updated on demand
        # 1 = eager: the cell value is to be updated immediatly
        self.mode = dict()

        # the state 
        # 0 = dirty: the cell value is inconsistent with its dependencies or formula
        # 1 = clean: the cell value is up-to-date
        self.state = dict()

        # this is the stack of evaluated element
        self.evaluation_stack = []

        # a global lock on entry functions
        self.glock = Lock()
        
        # defining a global
        if _globals == None:
            self._globals = globals()
        else:
            self._globals = _globals

    # draw the graph
    def show_graph(self):
        nx.draw_spring(self.G)    
        plt.show()


    # update an element, and return its value
    def update(self, key):

        #print "update(" + str(key) + ")"
        
        # if we have a formula, we need to recompute ourselves
        if self.formulas[key] <> None:

            # we remove all predecessors
            try:
                for i in self.G.predecessors(key):
                    self.remove_edge((i, key))
            except:
                pass
        
            # we push the key on the stack
            self.evaluation_stack.append(key)

            # we evaluate the formula with ourselves as local
            try:
                value = eval(self.formulas[key], self._globals, self)
            except Exception as e:
                # we have an exception, we pop from the evaluation stack
                self.evaluation_stack.pop()
                # and raise the exception
                raise e

            # everything is fine, we update the value
            self.values[key] = value

            # we pop from the evaluation stack
            self.evaluation_stack.pop()

        # we set to clean
        self.state[key] = 1

        # we call the callbacks
        try:
            for i in self.callbacks(key):
                i("update", (key, value))
        except:
            pass

        # and we set all possible successor to dirty state
        for i in nx.topological_sort(self.G, [key]):
            if i <> key:
                #print str(key) + " -> " + str(i)
                self.state[i] = 0
            
        # and finally return
        return

    # setting a value
    def __setitem__(self, key, value):

        #a special case: self
        if key == "self":
            raise KeyError

        #print "__setitem__(" + str(key) + ", " + str(value) + ")__"
        #print "evaluation_stack := " + str(self.evaluation_stack) 
        
        # first we create the key if it does not exists
        if key not in self.state:

            self.G.add_node(key)
            # by default we put value eager
            self.mode[key] = 1
            # and dirty
            self.state[key] = 0
            # without callbacks
            self.callbacks[key] = []

        # then we look if we are a formula or a value
        if isinstance(value, str) and len(value) > 0 and value[0] == '=':
            self.formulas[key] = value[1:]
        else:
            self.formulas[key] = None
            self.values[key] = value

        # we update the value only if we are eager
        if self.mode[key] == 1:
            self.update(key)
            # forall our successor that are eager and dirty we update
            for i in nx.topological_sort(self.G, [key]):
                if i <> key:
                    #print str(key) + " -> " + str(i)
                    if self.mode[i] == 1 and self.state[i] == 0:
                        print "__setitem__ update"
                        self.update(i)

        else:
            self.state[key] = 0 




        return None

    # getting a value
    def __getitem__(self, key):

        #a special case: self
        if key == "self":
            return self

        #print "__getitem__(" + str(key) + ")__"
        #print "evaluation_stack := " + str(self.evaluation_stack) 

        # if we do not have the key, then we leave
        if key not in self.state:
            raise KeyError

        # if the key is dirty, we need to update it
        if self.state[key] == 0:
            #print "__getitem__ update"
            self.update(key)

        # if the stack is not empty, then we need to add an edge from the top of the stack to the current key 
        if len(self.evaluation_stack) <> 0:
            self.G.add_edge(key, self.evaluation_stack[len(self.evaluation_stack)-1])

        # and finally return the value
        return self.values[key]

    #delete an element
    def __delitem__(self, key):

        #a special case: self
        if key == "self":
            raise KeyError
        
        # if we do not have the key, then we leave
        if key not in self.state:
            raise KeyError
        
        # we mark all successor as dirty
        for i in nx.topological_sort(self.G, [key]):
            if i <> key:
                #print str(key) + " -> " + str(i)
                self.state[i] = 0

        # we remove the key
        self.G.remove_node(key)
        del self.formulas[key]
        del self.values[key]
        fs = self.callbacks[key]
        del self.callbacks[key]
        del self.mode[key]
        del self.state[key]

        # we call the callbacks
        try:
            for i in fs:
                i("delete", key)
        except:
            pass

    # returns keys
    def keys(self):
        return self.state.keys()

    # exec
    def store_exec(self, cmd):
        exec cmd in self._globals, self


if __name__ == '__main__':
  from math import sin, pi
  
  store = Storegraph(_globals = globals())

  store["caca"] = 1
  store["asd"] = "=caca + 3"
  store["asdf"] = "=caca + 4"
  store["coucou"] = "= asd + asdf + self[\"caca\"]"

  store.store_exec("from math import sin, pi")

  store["mypi"] = "= pi"

  store.show_graph()
  
  