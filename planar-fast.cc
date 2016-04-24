/* Find all cubic planar graphs with one triangle, two squares, five pentagons,
 * and arbitrarily many hexagons
 * This is planar (no outerstate), but without output besides total count.
 *  - Use sparse nauty: DONE
 *  - use BFS?  And, whenever we go up by a number of faces, we can throw out the canonical graphs
 *    (because they'll all be too small to match). Fewer to search --> faster.
 *  - use a cubic planar canonical labeler?
 * Timings for MAX_FACES=34:
 *   densenauty,            -O2 -march=native : 4m56.408s
 *     w/ twopaths,         -O2 -march=native : 1m31.677s
 *   sparsenauty,           -O2 -march=native : 3m24s 
 *     w/ schreier,         -O2 -march=native : 3m21s
 *     w/distances_sg 2,    -O2 -march=native : 1m24
 *     w/distances_sg 2,    -O3 -march=native : 1m25s
 *       w/ schreier,       -O2 -march=native : 1m34.450s
 *     w/distances_sg 3,    -O2 -march=native : 1m30.836s
 *       w/ schreier,       -O2 -march=native : 1m30s
 */
#include <vector>
#include <deque>
#include <set>
#include <algorithm>
#include "nausparse.h"

#ifndef MAX_FACES
#define MAX_FACES 12
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
typedef unsigned int uint;

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
        //options.schreier = TRUE;
            
        nauty_check(WORDSIZE,maxm,maxn,NAUTYVERSIONID);
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
        const int startF = edges[faces[fF][0]].v1,
                  endptF = edges[faces[fF].back()].v2;
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
                // Fall thru!
            case 6:
                // Add four edges: one to close next face, the two of the subsequent
                // face, and from there to the start point of F.
                edges.emplace_back(endptF, edges[faces[nF].back()].v2);
                faces[fF].push_back(edges.size() - 1);
                faces[nF].push_back(edges.size() - 1);

                countFace(faces[nF]);

                faces[fF].insert(faces[fF].end(), faces[nnF].begin(), faces[nnF].end());

                edges.emplace_back(startF, edges[faces[nnF].back()].v2);
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
                // Fall thru!
            case 7:
                // add four edges: one closing the previous face; the adjacent face to that
                //   has length two; from there to the end point of F
                edges.emplace_back(edges[faces[pF][0]].v1, startF);
                faces[fF].push_back(edges.size() - 1);
                faces[pF].push_back(edges.size() - 1);

                countFace(faces[pF]);

                faces[fF].insert(faces[fF].end(), faces[ppF].begin(), faces[ppF].end());

                edges.emplace_back(edges[faces[ppF][0]].v1, endptF);
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
                
                edges.emplace_back(endptF, edges[faces[nF].back()].v2);
                faces[fF].push_back(edges.size() - 1);
                
                faces[nF].push_back(edges.size() - 1);

                faces[fF].push_back(faces[nnF][0]);

                edges.emplace_back(++numverts, edges[faces[nnF].back()].v2);
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
                
                edges.emplace_back(edges[faces[pF][0]].v1, startF);
                faces[fF].push_back(edges.size() - 1);
                faces[pF].push_back(edges.size() - 1);

                faces[fF].push_back(faces[ppF][0]);

                edges.emplace_back(edges[faces[ppF][0]].v1, ++numverts);
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

        return facesoflen[3] == N_TRI &&
               facesoflen[4] == N_SQ &&
               facesoflen[5] == N_PENT;
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
        sortlists_sg(&canong);
    }

};

SG_DECL(GraphState::sg);
SG_DECL(GraphState::canong);
int *GraphState::lab, *GraphState::ptn, *GraphState::orbits;
DEFAULTOPTIONS_SPARSEGRAPH(GraphState::options);
statsblk GraphState::stats;

int main() {
    deque<GraphState> graphStack;
    std::set<vector<int>> canonslns;
    /* nauty canonical forms of solutions. */
    vector<int> nsuccess(MAX_FACES - 6); // allow for 'overslop' of 1 face
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
            pop = true;
            continue;
        }
        graphStack.push_back(G);
        G.addEdges();

        if (G.openfaces.empty()) {
            if (G.sizefinal() && G.faces.size() <= MAX_FACES) {
                G.canongraph();
                if (canonslns.emplace(G.canong.e, G.canong.e + G.canong.nde).second)
                    ++nsuccess[G.nhex];
                /* To write graph6 output, #include "gtools.h" and:
                    writeg6_sg(stdout, &G.canong);
                 */
            }
            pop = true;
            continue;
        }

        if (graphStack.size() > MAX_FACES - 4) {
            pop = true;
            continue;
        }
        if (G.openfaces.size() == 1) {
            pop = true;
            continue;
        }
        if (!G.sizecheck()) {
            pop = true;
            continue;
        }
        
        G.chooseFace();
    }
    for (int i = 1; i < MAX_FACES-7; ++i)
        printf("%d:  %d\n", i, nsuccess[i]);
    return 0;
}
