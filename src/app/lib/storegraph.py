import networkx as nx
import matplotlib.pyplot as plt
from threading import *
from pickle import *

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
        self.callbacks = []
        # the same, but callback are functions in the store here
        self.named_callbacks = []

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
                # everything is fine, we update the value
                self.values[key] = value

            except Exception as e:
                # and raise the exception
                self.values[key] = e

            # we pop from the evaluation stack
            self.evaluation_stack.pop()

        # we set to clean
        self.state[key] = 1

        # we call the callbacks
        for i in self.callbacks:
            try:
                i("update", (key, self.values[key]))
            except Exception as e:
                print "callback update " + key
                if self.formulas[key] <> None:
                    print ":= " + self.formulas[key]
                print "value :=" + str(self.values[key])
                print "callback :=" + str(i)
                print "error: " + str(e)
                pass

        for i in self.named_callbacks:
            try:
                self.__getitem__(i)(self, "update", (key, self.values[key]))
            except Exception as e:
                print "callback update " + key
                if self.formulas[key] <> None:
                    print ":= " + self.formulas[key]
                print "value :=" + str(self.values[key])
                print "callback :=" + str(i)
                print "error: " + str(e)
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

        print "__setitem__(" + str(key) + ", " + str(value) + ")__"
        #print "evaluation_stack := " + str(self.evaluation_stack) 
        
        # first we create the key if it does not exists
        if key not in self.G.nodes():

            self.G.add_node(key)
            # by default we put value eager
            self.mode[key] = 1
            # and dirty
            self.state[key] = 0
            
        # then we look if we are a formula or a value
        if isinstance(value, str) and len(value) > 0 and value[0] == '=':
            self.formulas[key] = value[1:]
            # we update the value only if we are eager
            if self.mode[key] == 1:
                self.update(key)
            else:
                self.state[key] = 0 

        else:
            self.formulas[key] = None
            self.values[key] = value

            # we call the callbacks
            for i in self.callbacks:
                try:
                    i("update", (key, self.values[key]))
                except Exception as e:
                    print "callback update " + key
                    if self.formulas[key] <> None:
                        print ":= " + self.formulas[key]
                    print "value :=" + str(self.values[key])
                    print "callback :=" + str(i)
                    print "error: " + str(e)
                    pass

            for i in self.named_callbacks:
                try:
                    self.__getitem__(i)(self, "update", (key, self.values[key]))
                except Exception as e:
                    print "callback update " + key
                    if self.formulas[key] <> None:
                        print ":= " + self.formulas[key]
                    print "value :=" + str(self.values[key])
                    print "callback :=" + str(i)
                    print "error: " + str(e)
                    pass

        # forall our successor that are eager and dirty we update
        for i in nx.topological_sort(self.G, [key]):
            if i <> key:
                if self.mode[i] == 1 and self.state[i] == 0:
                    self.update(i)

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

    # remove a key
    def remove_key(self, key):
        self.__delitem__(key)

    #delete an element
    def __delitem__(self, key):

        #a special case: self
        if key == "self":
            raise KeyError
        
        # if we do not have the key, then we leave
        if key not in self.state:
            raise KeyError
        
        # we remove the key
        #self.G.remove_node(key)
        del self.formulas[key]
        del self.values[key]
        #del self.mode[key]
        #del self.state[key]

        # we call the callbacks
        for i in self.callbacks:
            try:
                i("delete", key)
            except Exception as e:
                print "callback delete " + key
                print "callback :=" + str(i)
                print "error: " + str(e)
                pass

        for i in self.named_callbacks:
            try:
                self.__getitem__(i)(self, "delete", key)
            except Exception as e:
                print "callback delete " + key
                print "callback :=" + str(i)
                print "error: " + str(e)
                pass

        # we mark all successor as dirty
        for i in nx.topological_sort(self.G, [key]):
            if i <> key:
                #print str(key) + " -> " + str(i)
                self.state[i] = 0
                self.update(i)

        # if there is not successor, we remove the node, and mode and state
        if nx.topological_sort(self.G, [key]) == [key]:
            self.G.remove_node(key)
            del self.mode[key]
            del self.state[key]
                
    # returns keys
    def keys(self):
        return self.G.nodes()

    # exec
    def store_exec(self, cmd):
        exec cmd in self._globals, self

    # eval
    def store_eval(self, cmd):
        return eval(cmd, globals(), self)

    # add a calllback
    def add_callback(self, f):
        self.callbacks.append(f)

    # add a named calllback
    def add_named_callback(self, f):
        self.named_callbacks.append(f)

    # del a named calllback
    def del_named_callback(self, f):
        self.named_callbacks.remove(f)

    # getformula
    def getformula(self, key):
        if self.formulas[key] == None:
            return None
        else:
            return "=" + self.formulas[key]

    # getvalue
    def getvalue(self, key):
        return self.values[key]

    # save
    def save(self, file):
        # dump the data (we remove all values when there is a formula)
        formulas = dict()
        values = dict()
        for i in self.G.nodes():
            if self.formulas[i] <> None:
                formulas[i] = self.formulas[i]
            else:
                formulas[i] = None
                values[i] = self.values[i]

        dump((self.G, formulas, values, self.mode, self.state, self.named_callbacks), file, 1)

    def load(self, file):
        # load the data
        
        (self.G, self.formulas, self.values, self.mode, self.state, self.named_callbacks) = load(file)

        #for i in nx.topological_sort(self.G):
        #    print "node " + str(i) + ":= " + str(self.formulas[i])

        # we update all nodes with a formula
        for i in nx.topological_sort(self.G):
            if self.formulas[i] <> None:
                self.update(i)
    
if __name__ == '__main__':
  from math import sin, pi
  
  store = Storegraph(_globals = globals())

  store["caca"] = 1
  store["asd"] = "=caca + 3"
  store["asdf"] = "=caca + 4"
  store["coucou"] = "= asd + asdf + self[\"caca\"]"

  store["pi"] = "= __import__(\"math\").pi"

  store["doudou"] = "= pi + 3.14"

  store.save(open('ss4.pkl', 'wb'))

  store["mypi"] = "= pi"

  store.load(open('ss4.pkl', 'rb'))

  store.show_graph()
  
  
