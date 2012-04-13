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
    # return a pair of size(>0 -> buy | < 0 -> sell)/price
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

    # compute the pnl (in price) and upnl (in size)
    def pnl_upnl(self):
        pnl = 0
        upnl = 0
        for i in self.store["order"].keys():
            i = i[0]
            order = self.store["order"][i]
            pnl += -order[0] * order[1]
            upnl += order[0]

        upnl2 = upnl * self.store["bars"][self.store["nb bars"] - 1]["ajust. close"]
        return (pnl, upnl, upnl2, pnl + upnl2)


    #######################################################

    # a step function
    def step(self):
        
        # first we update
        self.update()
        
        # now a case analysis on the state
        st = self.store["state"]


        # we are closed, look for an entry signal
        if self.store["state"] == 0:
            entry_sig = self.entry()
            # we have one signal
            if entry_sig <> None:
                # we are now in opening state
                self.store["state"] = 1
                self.store["openingtime"] = self.store["nb bars"]
                # we create the order
                self.order(entry_sig[0], entry_sig[1])

                
        # we are opening, do we reach a time out?
        # (if the order is filled, a different thread should put us in opened state
        if self.store["state"] == 1:
            # if we have a time out, we check it does not expire
            if self.store["openingtimeout"] <> None:
                if self.store["openingtimeout"] + self.store["openingtime"] < self.store["nb bars"]:
                    # put ourselves in cancelling opening state and cancel the order
                    self.store["state"] = 2
                    self.cancel()
                    
        # we are cancelling opening, nothing to do
        if self.store["state"] == 2:
            pass

        # we are opened, look for an exit signal
        if self.store["state"] == 3:
            exit_sig = self.exit()
            # we have one signal
            if exit_sig <> None:
                # we are now in closing state
                self.store["state"] = 4
                self.store["closingtime"] = datetime.now()

                # we create the order
                self.close()

            
        # we are in closing, do we reach a time out?
        if self.store["state"] == 4:
            # if we have a time out, we check it does not expire
            if self.store["closingtimeout"] <> None:
                if self.store["closingtimeout"] + self.store["closingtime"] < self.store["nb bars"]:
                    # put ourselves in cancelling closing state and cancel the order
                    self.store["state"] = 5
                    self.cancel()

        # we are cancelling closing, nothing to do
        if self.store["state"] == 5:
            pass

        # just debug output
        if st <> self.store["state"]:
            print str(st) + " --> " + str(self.store["state"])

        # we are recording the pnl
        self.store["pnl"][self.store["nb bars"] - 1] = self.pnl_upnl()

# a first derivation: a backtest with pickled data
class BackTest(Strat):
    
    def __init__(self):
        # init the Strat
        Strat.__init__(self)

    # the order function
    def order(self, size, price):
        if price == None:
            price = self.store["bars"][self.store["nb bars"] - 1]["ajust. close"]
        self.store["order"][self.store["nb bars"] - 1] = (size, price)
        print "order: " + str((size, price)) + "@ " + str(self.store["bars"][self.store["nb bars"] - 1]["date"]) + " | " + str(self.store["nb bars"] - 1) + " ==> " + str(self.pnl_upnl())

        if self.store["state"] == 1:
            self.store["state"] = 3

        if self.store["state"] == 4:
            self.store["state"] = 0

        return None

    # the order close function
    def close(self):
        pos = self.pnl_upnl()[1]
        self.order(-pos, None) 
        return None

    # the cancel function
    def cancel(self):
        return None

    # run the backtest
    def run(self):
        for i in self.bars:
            #print i

            # add the bar
            self.store["bars"][self.store["nb bars"]] = i

            # increment the number of bar
            self.store["nb bars"] += 1

            # call the step
            self.step()

    def load(self, filename):
        # open the bars file and reverse it
        self.bars = load(open(filename, "rb"))
        self.bars.reverse()




# a first strat: look for order in several EMA
class Strat1(BackTest):
    
    def __init__(self):
        BackTest.__init__(self)

        self.store["nbema"] = 6
        
        for i in range(0, self.store["nbema"]):            
            if i == 0:
                self.store["ema"][i]["period"] = 5
            else:
                self.store["ema"][i]["period"] = self.store["ema"][i-1]["period"]*2
        
        print self.store["ema"]

    def entry(self):
        lema = []
        for i in range(0, self.store["nbema"]):
            lema.append(self.store["ema"][i]["value"][self.store["nb bars"] - 1])

        if self.is_lt_sorted(lema):            
            #print "lt_sorted: " + str(lema)
            return (-100, None)

        if self.is_gt_sorted(lema):            
            #print "gt_sorted: " + str(lema)
            return (100, None)

        return None

    # return a price
    def exit(self):
        lema = []
        for i in range(0, self.store["nbema"]):
            lema.append(self.store["ema"][i]["value"][self.store["nb bars"] - 1])

        if not (self.is_lt_sorted(lema) or self.is_gt_sorted(lema)):
            #print "unsorted: " + str(lema) 
            return True

        #print "sorted: " + str(lema) 

        return None


    # 
    def is_lt_sorted(self, l):

        if self.store["nb bars"] < self.store["ema"][self.store["nbema"] - 1]["period"]:
            return False

        for i in range(0, len(l)-1):
            #print lema.count(i)
            if l.count(l[i]) > 1:
                return False
        
        res = True

        for i in range(1, len(l)-1):
            res = res and l[i-1] < l[i]

        return res

    def is_gt_sorted(self, l):

        if self.store["nb bars"] < self.store["ema"][self.store["nbema"] - 1]["period"]:
            return False

        for i in range(0, len(l)-1):
            #print lema.count(i)
            if l.count(l[i]) > 1:
                return False
        
        res = True

        for i in range(1, len(l)-1):
            res = res and l[i-1] > l[i]

        return res


    # the update function
    def update(self):
        for i in range(0, self.store["nbema"]):
            index = self.store["nb bars"] - 1
            price = self.store["bars"][index]["ajust. close"]
            period = self.store["ema"][i]["period"]            
            try:
                lastema = self.store["ema"][i]["value"][index - 1]
                alpha = 2.0/(float(period)+1.0)
                newema = lastema * (1-alpha) + price * alpha
                self.store["ema"][i]["value"][index] = newema
            except Exception as e:
                #print e
                self.store["ema"][i]["value"][index] = price
       

        return None

# a second strat: look for an index in the ema such that the first segment is increasing and the other decreasing
class Strat2(BackTest):
    
    def __init__(self):
        BackTest.__init__(self)

        self.store["nbema"] = 6
        
        for i in range(0, self.store["nbema"]):            
            if i == 0:
                self.store["ema"][i]["period"] = 5
            else:
                self.store["ema"][i]["period"] = self.store["ema"][i-1]["period"]*2
        
        print self.store["ema"]
        self.store["index"] = []

    def entry(self):

        if self.store["nb bars"] < self.store["ema"][self.store["nbema"] - 1]["period"]:
            return None

        lema = []
        for i in range(0, self.store["nbema"]):
            lema.append(self.store["ema"][i]["value"][self.store["nb bars"] - 1])


        indexA = None
        # look for an index of /\ shape
        for i in range(0, self.store["nbema"]):

            if not self.is_lt_sorted(lema[0:i]):            
                continue
                
            if not self.is_gt_sorted(lema[i:len(lema)-1]):            
                continue

            if indexA == None:
                indexA = i
            else:
                indexA = max(indexA, i)

        indexV = None
        # look for an index of \/ shape
        for i in range(0, self.store["nbema"]):

            if not self.is_gt_sorted(lema[0:i]):            
                continue
                
            if not self.is_lt_sorted(lema[i:len(lema)-1]):            
                continue

            if indexV == None:
                indexV = i
            else:
                indexV = max(indexV, i)

        #if index <> None:
        #    print "increasing : " + str(lema[0:index])
        #    print "decreasing : " + str(lema[index:len(lema)-1])

        if indexA <> None:
            self.store["index"].append(indexA)

        if indexV <> None:
            self.store["index"].append(-indexV)

        if indexA == None and indexV == None:
            print "index == None in " + str(lema)

        return None

    # return a price
    def exit(self):

        if self.store["nb bars"] < self.store["ema"][self.store["nbema"] - 1]["period"]:
            return None

        lema = []
        for i in range(0, self.store["nbema"]):
            lema.append(self.store["ema"][i]["value"][self.store["nb bars"] - 1])

        if not (self.is_lt_sorted(lema) or self.is_gt_sorted(lema)):
            #print "unsorted: " + str(lema) 
            return True

        #print "sorted: " + str(lema) 

        return None


    # 
    def is_lt_sorted(self, l):

        if self.store["nb bars"] < self.store["ema"][self.store["nbema"] - 1]["period"]:
            return False

        for i in range(0, len(l)-1):
            #print lema.count(i)
            if l.count(l[i]) > 1:
                return False
        
        res = True

        for i in range(1, len(l)-1):
            res = res and l[i-1] < l[i]

        return res

    def is_gt_sorted(self, l):

        if self.store["nb bars"] < self.store["ema"][self.store["nbema"] - 1]["period"]:
            return False

        for i in range(0, len(l)-1):
            #print lema.count(i)
            if l.count(l[i]) > 1:
                return False
        
        res = True

        for i in range(1, len(l)-1):
            res = res and l[i-1] > l[i]

        return res


    # the update function
    def update(self):
        for i in range(0, self.store["nbema"]):
            index = self.store["nb bars"] - 1
            price = self.store["bars"][index]["ajust. close"]
            period = self.store["ema"][i]["period"]            
            try:
                lastema = self.store["ema"][i]["value"][index - 1]
                alpha = 2.0/(float(period)+1.0)
                newema = lastema * (1-alpha) + price * alpha
                self.store["ema"][i]["value"][index] = newema
            except Exception as e:
                #print e
                self.store["ema"][i]["value"][index] = price
       

        return None


if __name__ == "__main__":
    
    bt = Strat2()
    bt.load("8604.TSE")

    bt.run()
    
    print bt.pnl_upnl()
    print bt.store["index"]
    l = filter(lambda x: x <> None, bt.store["index"])
    print l
    
