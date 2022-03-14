class UnionFind:

    def __init__(self, N):
        self._id = [-1] * N
        self._count = N

    def find(self, x):
        if self._id[x] < 0:
            return x
        else:
            self._id[x] = self.find(self._id[x])
            return self._id[x]

    def connected(self, x, y):
        return self.find(x) == self.find(y)

    def union(self, x, y):
        if self._id[y] < self._id[x]:
            self._id[y] += self._id[x]
            self._id[x] = y
        else:
            self._id[x] += self._id[y]
            self._id[y] = x

    def __str__(self):
        return " ".join([str(x) for x in self._id])

    def __repr__(self):
        return "UnionFind(" + str(self) + ")"

