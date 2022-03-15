# Reference: https://algs4.cs.princeton.edu/15uf/UF.java.html
class UnionFind:

    def __init__(self, N):
        self._id = [i for i in range(N)]
        self._size = [1] * N
        self._count = N

    def find(self, x):
        while x != self._id[x]:
            x = self._id[x]
        return x

    def connected(self, x, y):
        return self.find(x) == self.find(y)

    def union(self, x, y):
        x = self.find(x)
        y = self.find(y)
        if x == y: return
        
        if self._size[x] > self._size[y]:
            self._id[y] = x
            self._size[x] += self._size[y]
        else:
            self._id[x] = y
            self._size[y] += self._size[x]

    def __str__(self):
        return " ".join([str(x) for x in self._id])

    def __repr__(self):
        return "UnionFind(" + str(self) + ")"