/* Find all cubic planar graphs with one triangle, two squares, five pentagons,
 * and arbitrarily many hexagons */
#include <iostream>
#include <iomanip>
#include <vector>
#include <deque>
#include <set>
#include <tuple>
#include <algorithm>
#include <cassert>
#include "nausparse.h"

/* Amount of blather on stdout: 0 to 3 */
#ifndef INFO_LVL
#define INFO_LVL 0
#endif

#ifndef MAX_FACES
#define MAX_FACES 14
#endif
/* Without a hard max, this version fails to detect looping and never gets anywhere.
 * On the other hand, versions with looping detection fail when given MAX_FACES
 * since the previously seen states were not fully explored. */

#define N_TRI  1
#define N_SQ   2
#define N_PENT 5
/* Don't be fooled: there are plenty of hard-wired numbers
 * which would have to be replaced by (N_PENT - 2) and so on,
 * and the assumption of a unique triangle is used throughout */

using std::vector;
using std::deque;
using std::cout;
typedef unsigned int uint;

#ifdef FLUSH
#define ENDL std::endl
#else
#define ENDL '\n'
#endif

#if INFO_LVL
#define LOG1(x) cout << x << ENDL
#else
#define LOG1(x)
#endif

#if INFO_LVL > 1
#define LOG2(x) cout << x << ENDL
#else
#define LOG2(x)
#endif

#if INFO_LVL > 2
#define LOG3(x) cout << x << ENDL
#else
#define LOG3(x)
#endif

#if MAX_FACES > 27
#define WIDTH 5
#elif MAX_FACES > 20
#define WIDTH 4
#elif MAX_FACES > 14
#define WIDTH 3
#else
#define WIDTH 2
#endif

template<typename T>
void commaprint(std::ostream& s, const T& vec) {
    bool first = true;
    for (auto& f : vec) {
        if (first) first = false;
        else s << ", ";
        s << f;
    }
}

struct edge {
    int v1, v2;
    edge(int va, int vb) : v1(va), v2(vb) {}
};

struct faceCounter {
    int ntri, nsq, npent;
    bool add(int size) {
        switch(size) {
            case 3:
                return ++ntri <= N_TRI;
            case 4:
                return ++nsq <= N_SQ;
            case 5:
                return ++npent <= N_PENT;
            case 6:
                return true;
            default:
                return false;
        }
    }
};

struct GraphState {
    int numverts, nsq, npent, nhex;
    vector<edge> edges;
    vector<deque<int>> faces;
    vector<int> openfaces;
    int medgadd, chosenFace;
/* medgadd: method to use to close the selected face (which is an open face
 * of the maximum size.)
 * 1: add one edge, from one open endpoint to the other
 * 2: add two edges, from the endpoints to a new vertex
 * 3: add three edges: one closing the next face; the adjacent face to that
 *    has length one; from there to the start point of F. Closes the graph
 *    if there are four faces.
 * 4: add three edges: one closing the previous face; the adjacent face to that
 *    has length one; from there to the end point of F. (Same as method 3 if
 *    there are four faces.)
 * 5: add three edges, with two new vertices
 * 6: add four edges: close next face; adjacent to that has length 2;
 *    thence back to start point of F. Closes the graph if we start with four faces.
 * 7: add four edges: close previous face; adjacent to that has length 2;
 *    thence back to end point of F. (Equivalent to 6 if we start with four faces.)
 * 8: add four edges: one closing the next face; the adjacent face to that
 *    has length one; from there and the start point of F to a new vertex
 * 9: add four edges: one closing the previous face; the adjacent face to that
 *    has length one; from there and the end point of F to a new vertex
 * 10: add four edges, with three new vertices */
#define NUM_METH 10
    static sparsegraph sg;
    static sparsegraph canong;
    static int *lab, *ptn, *orbits;
    static optionblk options;
    static statsblk stats;

    GraphState() : numverts{7}, nsq{0}, npent{0}, nhex{1},
      edges{ {1,2},
             {2,3},
             {1,3},
             {3,4},
             {4,5},
             {5,6},
             {6,7},
             {7,1} },
      faces{ {0,1,2},
             {2,3,4,5,6,7},
             {7,0},
             {1,3},
             {4}, {5}, {6} },
      openfaces{2,3,4,5,6},
      medgadd{0}, chosenFace{0} {
        int maxn = 2 * MAX_FACES; // allows for 'overslop' of 2 faces
        int maxm = (maxn+WORDSIZE-1)/WORDSIZE;
        lab = new int[maxn];
        ptn = new int[maxn];
        orbits = new int[maxn];

        options.getcanon = TRUE;
        options.invarproc = distances_sg;
        options.invararg = 2;
            
        nauty_check(WORDSIZE,maxm,maxn,NAUTYVERSIONID);
    }

    int startpt(const deque<int>& face) const {
        // This only works for open faces, since we don't bother keeping closed
        // faces in cyclic order.
        const edge& first = edges[face[0]];
        if (face.size() == 1)
            return first.v1;
        const edge& sec = edges[face[1]];
        assert (first.v1 != sec.v1 && first.v1 != sec.v2);
        return first.v1;
    }

    int endpt(const deque<int>& face) const {
        // Only for open faces (like startpt)
        auto rit = face.crbegin();
        const edge& laste = edges[*rit];
        if (face.size() == 1)
            return laste.v2;
        const edge& pene = edges[*(++rit)];
        assert(laste.v2 != pene.v1 && laste.v2 != pene.v2);
        return laste.v2;
    }

    void countFace(const deque<int>& face) {
        switch (face.size()) {
            case 4:
                ++nsq;
                break;
            case 5:
                ++npent;
                break;
            case 6:
                ++nhex;
                break;
            default:
                std::cerr << "**Face of size " << face.size() << "!\n";
        }
    }

    bool isValid(int oF, int meth) const {
        const int n = openfaces.size();
        const int pppoF = (oF + 2*n - 3) % n,
             ppoF = (oF + n - 2) % n,
             poF = (oF + n - 1) % n,
             noF = (oF + 1) % n,
             nnoF = (oF + 2) % n,
             nnnoF = (oF + 3) % n;
        const deque<int> &pppF = faces[openfaces[pppoF]],
             &prprF = faces[openfaces[ppoF]],
             &prevF = faces[openfaces[poF]],
             &F = faces[openfaces[oF]],
             &nextF = faces[openfaces[noF]],
             &nnF = faces[openfaces[nnoF]],
             &nnnF = faces[openfaces[nnnoF]];
        faceCounter facect = {1, nsq, npent};
        assert(F.size() > 1);
		switch(meth) {
           case 0:
                return false;
           case 1:
                // add one edge, from one open endpoint to the other.
                if (n > 2 && (prevF.size() + nextF.size() > 4)) return false;
                if (n == 2 && !facect.add(nextF.size() + 1)) return false;
                return facect.add(F.size() + 1);
           case 2:
                // add two edges, from the endpoints to a new vertex
                if (prevF.size() > 4) return false;
                if (nextF.size() > 4) return false;
                return facect.add(F.size() + 2);
            case 3:
                // add three edges: one closing the next face; the adjacent face
                // to that has length one; from there to the start point of F
                if (n < 4 || n == 5) return false;
                if (nnF.size() != 1) return false;
                if (!facect.add(nextF.size() + 1)) return false;
                if (n > 4 && (prevF.size() + nnnF.size() > 4)) return false;
                if (n == 4 && !facect.add(prevF.size() + 1)) return false;
                return facect.add(F.size() + 3);
            case 4:
                // add three edges: one closing the previous face; the adjacent
                // face to that has length one; from there to the end point of F
                if (n < 6) return false; // when n == 4, this is case 3.
                if (prprF.size() != 1) return false;
                if (!facect.add(prevF.size() + 1)) return false;
                if (n > 4 && (pppF.size() + nextF.size() > 4)) return false;
                if (n == 4 && !facect.add(nextF.size() + 1)) return false;
                return facect.add(F.size() + 3);
            case 5:
                // add three edges, with two new vertices
                if (prevF.size() > 4) return false;
                if (nextF.size() > 4) return false;
                return facect.add(F.size() + 3);
            case 6:
                // add four edges: one to close next face, across the two edges of the
                // subsequent face, then back to start point of F. Closes if n == 4
                if (n < 4 || n == 5) return false;
                if (nnF.size() != 2) return false;
                if (!facect.add(nextF.size() + 1)) return false;
                if (n > 4 && (prevF.size() + nnnF.size() > 4)) return false;
                if (n == 4 && !facect.add(prevF.size() + 1)) return false;
                return facect.add(F.size() + 4);
            case 7:
                // add four edges: one to close previous face, across the two edges of the
                // preceding face, then back to endpoint of F.
                if (n < 6) return false; // when n == 4, this is case 6.
                if (prprF.size() != 2) return false;
                if (!facect.add(prevF.size() + 1)) return false;
                if (n > 4 && (pppF.size() + nextF.size() > 4)) return false;
                if (n == 4 && !facect.add(nextF.size() + 1)) return false;
                return facect.add(F.size() + 4);
            case 8:
                // add four edges: one closing the next face; the adjacent face
                // to that has length one; from there and the start point of F
                // to a new vertex
                if (n < 5) return false;
                if (nnF.size() != 1) return false;
                if (prevF.size() > 4) return false;
                if (nnnF.size() > 4) return false;
                if (!facect.add(nextF.size() + 1)) return false;
                return facect.add(F.size() + 4);
            case 9:
                // add four edges: one closing the previous face; the adjacent
                // face to that has length one; from there and the end point of
                // F to a new vertex
                if (n < 5) return false;
                if (prprF.size() != 1) return false;
                if (nextF.size() > 4) return false;
                if (pppF.size() > 4) return false;
                if (!facect.add(prevF.size() + 1)) return false;
                return facect.add(F.size() + 4);
            case 10:
                // add four edges, with three new vertices
                if (prevF.size() > 4) return false;
                if (nextF.size() > 4) return false;
                return facect.add(F.size() + 4);
            default:
                return false;
		}
    }

    bool isValid() const {
        return isValid(chosenFace, medgadd);
    }

    bool incMethod() {
        while (medgadd <= NUM_METH) {
            ++medgadd;
            if (isValid()) return true;
        }
        return false;
    }

    void addEdges(int oF, int meth) {
        // oF: index to openfaces
        const int n = openfaces.size();
        const int pppoF = (oF + 2*n - 3) % n,
            ppoF = (oF + n - 2) % n,
            poF = (oF + n - 1) % n,
            noF = (oF + 1) % n,
            nnoF = (oF + 2) % n,
            nnnoF = (oF + 3) % n;
        const int pppF = openfaces[pppoF],
            ppF = openfaces[ppoF],
            pF = openfaces[poF],
            fF = openfaces[oF],
            nF = openfaces[noF],
            nnF = openfaces[nnoF],
            nnnF = openfaces[nnnoF];
        const int startF = startpt(faces[fF]),
                  endptF = endpt(faces[fF]);
        vector<int> toerase;
        switch(meth) {
            case 1:
                // add one edge, from one open endpoint to the other.
                edges.emplace_back(startF,endptF);
                faces[fF].push_back(edges.size() - 1);
                faces[pF].push_back(edges.size() - 1);
                if (noF > oF) {
                    openfaces.erase(openfaces.begin() + oF, openfaces.begin() + oF + 2);
                } else {
                    openfaces.erase(openfaces.begin() + oF);
                    openfaces.erase(openfaces.begin() + noF);
                }
                if (n == 2) {
                    // prevF = nextF, and that face is also closed
                    countFace(faces[pF]);
                    break;
                }
                faces[pF].insert(faces[pF].end(), faces[nF].begin(), faces[nF].end());
                toerase.push_back(nF);
                break;
            case 2:
                // add two edges, from the endpoints to a new vertex
                edges.emplace_back(startF,++numverts);
                faces[pF].push_back(edges.size() - 1);
                
                edges.emplace_back(numverts,endptF);
                faces[fF].push_back(edges.size() - 1);
                faces[fF].push_back(edges.size() - 2);
                faces[nF].push_front(edges.size() - 1);
                
                openfaces.erase(openfaces.begin() + oF);
                break;
            case 3:
                // add three edges: one closing the next face; the adjacent face to that
                // has length one; from there to the start point of F.
                // Closes the graph if n == 4.
                assert(faces[nnF].size() == 1);
                // Fall thru!
            case 6:
                // Add four edges: one to close next face, the two of the subsequent
                // face, and from there to the start point of F.
                edges.emplace_back(endptF, endpt(faces[nF]));
                faces[fF].push_back(edges.size() - 1);
                faces[nF].push_back(edges.size() - 1);

                countFace(faces[nF]);

                faces[fF].insert(faces[fF].end(), faces[nnF].begin(), faces[nnF].end());

                edges.emplace_back(startF, endpt(faces[nnF]));
                faces[fF].push_back(edges.size() - 1);
                faces[pF].push_back(edges.size() - 1);
                
                // Erase oF, noF, nnoF, nnnoF from openfaces.
                if (nnnoF > oF) {
                    openfaces.erase(openfaces.begin() + oF, openfaces.begin() + oF + 4);
                } else if (nnoF > oF) {
                    openfaces.erase(openfaces.begin() + oF, openfaces.begin() + oF + 3);
                    openfaces.erase(openfaces.begin() + nnnoF);
                } else if (noF > oF) {
                    openfaces.erase(openfaces.begin() + oF, openfaces.begin() + oF + 2);
                    openfaces.erase(openfaces.begin() + nnoF, openfaces.begin() + nnoF + 2);
                } else { 
                    openfaces.erase(openfaces.begin() + oF);
                    openfaces.erase(openfaces.begin() + noF, openfaces.begin() + noF + 3);
                }
                // nnF has been absorbed by F.
                toerase.push_back(nnF);
                
                if (n == 4) {
                    // prevF = nnnF, and that face is also closed
                    countFace(faces[pF]);
                    break;
                }
                // otherwise, prevF absorbs nnnF
                faces[pF].insert(faces[pF].end(), faces[nnnF].begin(), faces[nnnF].end());
                toerase.push_back(nnnF);
                break;
            case 4:
                // add three edges: one closing the previous face; the adjacent face to that
                //   has length one; from there to the end point of F
                assert(faces[ppF].size() == 1);
                // Fall thru!
            case 7:
                // add four edges: one closing the previous face; the adjacent face to that
                //   has length two; from there to the end point of F
                assert(endpt(faces[pF]) == startF);
               
                edges.emplace_back(startpt(faces[pF]), startF);
                faces[fF].push_back(edges.size() - 1);
                faces[pF].push_back(edges.size() - 1);

                countFace(faces[pF]);

                faces[fF].insert(faces[fF].end(), faces[ppF].begin(), faces[ppF].end());

                edges.emplace_back(startpt(faces[ppF]), endptF);
                faces[fF].push_back(edges.size() - 1);
                faces[pppF].push_back(edges.size() - 1);
                
                // Erase ppoF, poF, oF, noF from openfaces.
                if (ppoF < noF) {
                    openfaces.erase(openfaces.begin() + ppoF, openfaces.begin() + noF + 1);
                } else if (poF < noF) {
                    openfaces.erase(openfaces.begin() + ppoF);
                    openfaces.erase(openfaces.begin() + poF, openfaces.begin() + noF + 1);
                } else if (oF < noF) {
                    openfaces.erase(openfaces.begin() + ppoF, openfaces.begin() + poF + 1);
                    openfaces.erase(openfaces.begin() + oF, openfaces.begin() + noF + 1);
                } else { 
                    openfaces.erase(openfaces.begin() + ppoF, openfaces.begin() + oF + 1);
                    openfaces.erase(openfaces.begin() + noF);
                }
                // ppF has been absorbed by F.
                toerase.push_back(ppF);

                if (n == 4) {
                    // pppF = nF, and that face is also closed
                    countFace(faces[nF]);
                    break;
                }
                // otherwise, pppF absorbs nF
                faces[pppF].insert(faces[pppF].end(), faces[nF].begin(), faces[nF].end());
                toerase.push_back(nF);
                break;
            case 5:
                // add three edges, with two new vertices
                edges.emplace_back(startF,++numverts);
                faces[pF].push_back(edges.size() - 1);

                ++numverts;
                edges.emplace_back(numverts-1,numverts);
                faces.emplace_back(1,edges.size() - 1);
                openfaces[oF] = faces.size() - 1;

                edges.emplace_back(numverts,endptF);
                faces[fF].push_back(edges.size() - 1);
                faces[fF].push_back(edges.size() - 2);
                faces[fF].push_back(edges.size() - 3);
                faces[nF].push_front(edges.size() - 1);
                break;
            case 8:
                // add four edges: one closing the next face; the adjacent face to that
                //    has length one; from there and the start point of F to a new vertex
                assert(faces[nnF].size() == 1);
                assert(endptF == startpt(faces[nF]));
                
                edges.emplace_back(endptF, endpt(faces[nF]));
                faces[fF].push_back(edges.size() - 1);
                
                assert(endpt(faces[nnF]) != endpt(faces[nF]));
                faces[nF].push_back(edges.size() - 1);

                faces[fF].push_back(faces[nnF][0]);

                edges.emplace_back(++numverts, endpt(faces[nnF]));
                faces[fF].push_back(edges.size() - 1);
                faces[nnnF].push_front(edges.size() - 1);
                
                edges.emplace_back(startF, numverts);
                faces[fF].push_back(edges.size() - 1);
                faces[pF].push_back(edges.size() - 1);

                if (nnoF > oF) {
                    openfaces.erase(openfaces.begin() + oF, openfaces.begin() + oF + 3);
                } else if (noF > oF) {
                    openfaces.erase(openfaces.begin() + oF, openfaces.begin() + oF + 2);
                    openfaces.erase(openfaces.begin() + nnoF);
                } else { 
                    openfaces.erase(openfaces.begin() + oF);
                    openfaces.erase(openfaces.begin() + noF, openfaces.begin() + noF + 2);
                }
                countFace(faces[nF]);
                toerase.push_back(nnF);
                break;
            case 9:
                // add four edges: one closing the previous face; the adjacent face to that
                //    has length one; from there and the end point of F to a new vertex
                assert(faces[ppF].size() == 1);
                assert(endpt(faces[pF]) == startF);
                
                edges.emplace_back(startpt(faces[pF]), startF);
                faces[fF].push_back(edges.size() - 1);
                faces[pF].push_back(edges.size() - 1);

                faces[fF].push_back(faces[ppF][0]);

                assert(startpt(faces[ppF]) != startpt(faces[pF]));

                edges.emplace_back(startpt(faces[ppF]), ++numverts);
                faces[fF].push_back(edges.size() - 1);
                faces[pppF].push_back(edges.size() - 1);
                
                edges.emplace_back(numverts, endptF);
                faces[fF].push_back(edges.size() - 1);
                faces[nF].push_front(edges.size() - 1);

                if (ppoF < oF) {
                    openfaces.erase(openfaces.begin() + ppoF, openfaces.begin() + oF + 1);
                } else if (poF < oF) {
                    openfaces.erase(openfaces.begin() + ppoF);
                    openfaces.erase(openfaces.begin() + poF, openfaces.begin() + oF + 1);
                } else { 
                    openfaces.erase(openfaces.begin() + ppoF, openfaces.begin() + poF + 1);
                    openfaces.erase(openfaces.begin() + oF);
                }
                countFace(faces[pF]);
                toerase.push_back(ppF);
                break;
            case 10:
                // add four edges, with three new vertices
                edges.emplace_back(startF,++numverts);
                faces[fF].push_back(edges.size() - 1);
                faces[pF].push_back(edges.size() - 1);
                
                ++numverts;
                edges.emplace_back(numverts-1, numverts);
                faces[fF].push_back(edges.size() - 1);
                faces.emplace_back(1, edges.size() - 1);
                openfaces.insert(openfaces.begin() + oF, faces.size() - 1);

                ++numverts;
                edges.emplace_back(numverts-1,numverts);
                faces[fF].push_back(edges.size() - 1);
                faces.emplace_back(1, edges.size() - 1);
                openfaces[oF+1] = faces.size() - 1;

                edges.emplace_back(numverts,endptF);
                faces[fF].push_back(edges.size() - 1);
                faces[nF].push_front(edges.size() - 1);
                break;
            default:
                assert(false);
        }
        countFace(faces[fF]);
        std::sort(toerase.rbegin(), toerase.rend());
        for (const int& ef : toerase) {
            for (int& of : openfaces)
                if (of > ef)
                    --of;
            faces.erase(faces.begin() + ef);
        }
    }

    void addEdges() {
        addEdges(chosenFace, medgadd);
    }

    void chooseFace() {
        chosenFace = 0;
        for (uint i = 1; i < openfaces.size(); ++i)
            if (faces[openfaces[i]].size() > faces[openfaces[chosenFace]].size())
                chosenFace = i;
        medgadd = 0;
    }

    bool sizecheck() const {
        int facesoflen [7] = {};
        for (auto& F : faces) {
            if (F.size() > 6)
                return false;
            ++facesoflen[F.size()];
        }
        for (int o : openfaces) {
            if (faces[o].size() > 5)
                return false;
            --facesoflen[faces[o].size()];
        }
        if (facesoflen[0] || facesoflen[1] || facesoflen[2])
            return false;
        assert (facesoflen[3] == 1 &&
                facesoflen[4] == nsq &&
                facesoflen[5] == npent &&
                facesoflen[6] == nhex);
        return facesoflen[3] <= N_TRI &&
               facesoflen[4] <= N_SQ &&
               facesoflen[5] <= N_PENT;
    }
    
    bool sizefinal() const {
        int facesoflen [7] = {};
        for (auto& F : faces) {
            if (F.size() < 3 || F.size() > 6)
                return false;
            ++facesoflen[F.size()];
        }
        assert (facesoflen[3] == 1 &&
                facesoflen[4] == nsq &&
                facesoflen[5] == npent &&
                facesoflen[6] == nhex);
        int vertdegs [numverts+1] = {};
        for (const edge& e : edges) {
            ++vertdegs[e.v1];
            ++vertdegs[e.v2];
        }
        if (vertdegs[0])
            std::cerr << "**Vertex 0?!\n";
        if (*std::min_element(vertdegs + 1, vertdegs + numverts + 1) != 3 ||
            *std::max_element(vertdegs + 1, vertdegs + numverts + 1) != 3) {
            std::cerr << "**Not cubic\n";
            return false;
        }

        return facesoflen[3] == N_TRI &&
               facesoflen[4] == N_SQ &&
               facesoflen[5] == N_PENT;
    }

    void printnbrs(std::ostream& s, uint face) const {
        vector<int> nbrs;
        for (int e : faces[face]) {
            int numfound = 0;
            for (uint f = 0; f < faces.size(); ++f) {
                if (f == face) continue;
                if (std::find(faces[f].begin(), faces[f].end(), e) != faces[f].end()) {
                    nbrs.push_back(faces[f].size());
                    ++numfound;
                }
            }
            assert(numfound == 1);
        }
        commaprint(s, nbrs);
    }

    void canongraph() const {
        SG_ALLOC(sg, numverts, 3*numverts, "oops");

        sg.nv = numverts;
        sg.nde = 2*edges.size();

        for (int i = 0; i < numverts; ++i) {
            sg.v[i] = 3*i;
            sg.d[i] = 0;
        }

        for (const edge& e : edges) {
            sg.e[sg.v[e.v1-1]+sg.d[e.v1-1]] = e.v2 - 1;
            ++sg.d[e.v1-1];
            sg.e[sg.v[e.v2-1]+sg.d[e.v2-1]] = e.v1 - 1;
            ++sg.d[e.v2-1];
        }
        
        sparsenauty(&sg,lab,ptn,orbits,&options,&stats,&canong);
     /* values in lab list the vertices of sg in order to get canong.
      * The size of the group is returned in stats.grpsize1 and
      * stats.grpsize2. */
        if (stats.errstatus)
            std::cerr << "**Oh no, nauty error " << stats.errstatus << '\n';
        sortlists_sg(&canong);
    }
};

SG_DECL(GraphState::sg);
SG_DECL(GraphState::canong);
int *GraphState::lab, *GraphState::ptn, *GraphState::orbits;
DEFAULTOPTIONS_SPARSEGRAPH(GraphState::options);
statsblk GraphState::stats;

std::ostream& operator<<(std::ostream& s, const GraphState& gs) {
    s << "  tri: ";
    gs.printnbrs(s,0);
    for (uint i = 0; i < gs.faces.size(); ++i) {
        if (gs.faces[i].size() == 4) {
            s << "  sqr: ";
            gs.printnbrs(s,i);
        }
    }
    s << "  " << std::setw(2) << gs.nhex << " hexes, " << gs.numverts << " verts";
    return s;
}

void seestack(const deque<GraphState>& graphStack) {
  /* To examine the stack e.g. after breaking, or in gdb */
    for (const auto& gs : graphStack) {
        cout << gs.nsq << ", " << gs.npent << ", " << gs.nhex << ". Method "
            << gs.medgadd << " on face " << gs.openfaces[gs.chosenFace] 
            << " (" << gs.chosenFace << ")\t[";
        for (int o : gs.openfaces)
            cout << gs.faces[o].size() << ", ";
        cout << "]" << ENDL;
    }
}

int main() {
    std::ios_base::sync_with_stdio(false);

    deque<GraphState> graphStack;
    std::set<vector<int>> canonslns;
    /* nauty canonical forms of solutions. */
    uint nsuccess = 0;
    GraphState G{};
    
    bool pop = false;
    for(;;) {
        if (pop) {
            if (graphStack.empty())
                break;
            G = graphStack.back();
            graphStack.pop_back();
            pop = false;
        }
        if (!G.incMethod()) {
            LOG3( "Can't close face " << G.openfaces[G.chosenFace] );
            pop = true;
            continue;
        }
        graphStack.push_back(G);
        LOG3( "Method " << G.medgadd << " on face " << G.openfaces[G.chosenFace] );
        G.addEdges();

       #if INFO_LVL > 1
         cout << "Face lengths: ";
         bool first = true;
         for (auto& f : G.faces) {
             if (first) first = false;
             else cout << ", ";
             first = false;
             cout << f.size();
         }
         cout << ".  Open faces: ";
         commaprint(cout, G.openfaces);
         cout << ENDL;
       #endif

        if (G.faces[2].size() > 4)
            if (std::find(G.openfaces.begin(), G.openfaces.end(), 3) == G.openfaces.end())
                if (G.faces[3].size() < G.faces[2].size()) {
                    // we should have seen this case when face 2 was a square or pent
                    pop = true;
                    continue;
                }

        if (G.openfaces.empty()) {
            pop = true;
            if (G.faces.size() > MAX_FACES) continue;
            if (G.sizefinal()) {
                G.canongraph();
                if (canonslns.emplace(G.canong.e, G.canong.e + G.canong.nde).second) {
                    ++nsuccess;
                    cout << std::setw(WIDTH) << nsuccess << ". " << G << ENDL;
                   /* for (auto rit = graphStack.rbegin(); rit != graphStack.rend(); ++ rit)
                        rit->leadsup = true; */
                } else {
                    LOG1( "  ! " << G << " Seen before." );
                }
            } else {
                cout << "Whoops\n";
            }
            continue;
        }

        if (graphStack.size() > MAX_FACES - 4) {
            // should check nhex or numverts instead??
            LOG2( "Curtailing max faces" );
            pop = true;
            continue;
        }

        if (G.openfaces.size() == 1) {
            LOG3( "Single open vert" );
            pop = true;
            continue;
        }
        if (!G.sizecheck()) {
            LOG1( "Bad size" );
            pop = true;
            continue;
        }
        
        G.chooseFace();
        LOG3( "Chosen face " << G.chosenFace << " (" << G.openfaces[G.chosenFace] << ')' );
    }
    cout << "Total " << nsuccess << " solutions found, with up to " << MAX_FACES << " faces.\n";
    return 0;
}

