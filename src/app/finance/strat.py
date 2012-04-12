from storegraph import Storegraph
from gspeech import speack
from googlesheet import GoogleSheet
from datetime import *

from pickle import *

class Strat():

    def __init__(self):

        self.store = Storegraph(_globals = globals())

        #the state of the automaton
        # 0 := closed
        # 1 := opening
        # 2 := cancelling opening
        # 3 := opened
        # 4 := closing
        # 5 := cancelling closing
        self.store["state"] = 0

        # the opening/closing time out (default: None)
        self.store["openingtimeout"] = None
        self.store["closingtimeout"] = None

        # the number of bar so far
        self.store["nb bars"] = 0

    #######################################################
    # the function of the strategy 

    # the entry/exit signal emitting functions
    # return a pair of size/price/(long := 1 | short := -1)
    def entry(self):
        return None

    # return a price
    def exit(self):
        return None

    # the update function
    def update(self):
        return None

    #######################################################
    # the brokers functions

    # the order function
    def order(self, size, price):
        return None

    # the order close function
    def close(self):
        return None

    # the cancel function
    def cancel(self):
        return None

    #######################################################

    # a step function
    def step(self):
        
        # first we update
        self.update()
        
        # now a case analysis on the state

        # we are closed, look for an entry signal
        if self.store["state"] == 0:
            entry_sig = self.entry()
            # we have one signal
            if entry_sig <> None:
                # we are now in opening state
                self.state["state"] = 1
                self.state["openingtime"] = self.store["nb bars"]
                # we create the order
                self.order(entry_sig[0], entry_sig[1])

                
        # we are opening, do we reach a time out?
        # (if the order is filled, a different thread should put us in opened state
        if self.store["state"] == 1:
            # if we have a time out, we check it does not expire
            if self.store["openingtimeout"] <> None:
                if self.state["openingtimeout"] + self.store["openingtime"] < self.store["nb bars"]:
                    # put ourselves in cancelling opening state and cancel the order
                    self.cancel()
                    self.store["state"] = 2
                    
        # we are cancelling opening, nothing to do
        if self.store["state"] == 2:
            pass

        # we are opened, look for an exit signal
        if self.store["state"] == 3:
            exit_sig = self.exit()
            # we have one signal
            if exit_sig <> None:
                # we create the order
                self.close()

                # we are now in closing state
                self.state["state"] = 4
                self.state["closingtime"] = datetime.now()
            
        # we are in closing, do we reach a time out?
        if self.store["state"] == 4:
            # if we have a time out, we check it does not expire
            if self.store["closingtimeout"] <> None:
                if self.state["closingtimeout"] + self.store["closingtime"] < self.store["nb bars"]:
                    # put ourselves in cancelling closing state and cancel the order
                    self.cancel()
                    self.store["state"] = 5

        # we are cancelling closing, nothing to do
        if self.store["state"] == 5:
            pass

# a first derivation: a backtest with pickled data
class BackTest(Strat):
    
    def __init__(self, filename):
        # init the Strat
        Strat.__init__(self)

        # open the bars file and reverse it
        self.bars = load(open(filename, "rb"))
        self.bars.reverse()

    # the order function
    def order(self, size, price, side):
        return None

    # the order close function
    def close(self):
        return None

    # the cancel function
    def cancel(self):
        return None

    # run the backtest
    def run(self):
        for i in self.bars:
            print i

            # add the bar
            self.store["bars"][self.store["nb bars"]] = i

            # increment the number of bar
            self.store["nb bars"] += 1

            # call the step
            self.step()

if __name__ == "__main__":
    
    bt = BackTest("8604.TSE")

    bt.run()
    
    print bt.store["pnl"]
    
