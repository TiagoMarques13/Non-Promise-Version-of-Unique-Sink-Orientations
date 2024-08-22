#include<iostream>
#include<vector>
#include<unordered_map>
#include<unordered_set>
#include<algorithm>
#include<fstream>

using namespace std;

struct history
{
    /**
     * A structure for a history, given by two vectors of the known points and their values.
     */

    vector<int> points = {};
    vector<int> values = {};
};

struct sequence
{
    /**
     * A structure for a sequence, given by two vectors of the known points and their values and the next point.
     */

    vector<int> points = {};
    vector<int> values = {};
    int next_point = -1;
};

struct automorphism
{
    /**
     * A structure for the automorphisms of the hypercube.
     * It can be represented by a permutation pi of the dimensions and the point A which is sent to 0^n.
     */

    vector<int> pi;
    int A;
};

const int N = 3; // the dimension of the hypercube
vector<automorphism> all_automorphisms; // a vector containing all automorphisms of the hypercube
vector<vector<int>> all_outmaps = {{}}; // a vector containing all possible outmaps
vector<vector<int>> all_outmaps_symmetry = {}; // a vector containing all possible outmaps up to automorphisms
vector<history> all_histories_symmetry = {}; // a vector containing all histories up to automorphism
vector<sequence> all_sequences_symmetry = {}; // a vector containing all sequences up to automorphism
vector<unordered_map<int, int>> payoff; // a map from each sequence and outmap to its payoff
vector<int> stabilizer; // the number of automorphisms which fix a given orientation
int best_outmap[(1<<(N*(1<<N)))]; // a map from each orientation to the first orientation it is isomorphic to
vector<int> must_pick_this_one; // given a history, the vertex that must be picked to finish the game, or -1 if none exist
vector<string> constraints; // the constraints of the resulting linear program

string representation(sequence &S)
{
    /**
     * A string representation of each sequence, as a variable in the linear program.
     */

    string ans = "x";
    for (int i=0; i<S.points.size(); i++)
        ans += "" + to_string(S.points[i]) + "" + to_string(S.values[i]) + "";
    ans += to_string(S.next_point) + "";
    return ans;
}

void writeFileLP(const string &filename, const vector<string> &constraints)
{
    /**
     * A function which writes the constraints in a .lp file.
     */

    ofstream file(filename);

    file << "Minimize\n";
    file << " obj: v\n";

    file << "Subject To\n";
    for (int i=0; i<constraints.size(); i++){
        file << " c" << i+1 << ": ";
        file << constraints[i] << '\n';
    }

    file << "Bounds\n";
    file << " 0 <= v\n";
    for (auto S: all_sequences_symmetry)
        file << " 0 <= " << representation(S) << '\n';

    file << "End\n";

    file.close();
}

int outmap_to_int(vector<int> &outmap)
{
    /**
     * A map from an outmap to an integer representing it.
     */

    int ans = 0;
    for(auto u: outmap)
        ans = ans * (1<<N) + u;
    return ans;
}

int automorphism_point(automorphism &phi, int X)
{
    /**
     * The image of a point X under an automorphism phi.
     */

    X ^= phi.A;
    int ans = 0;
    for (int i=0; i<N; i++) if ((X&(1<<i)))
        ans |= (1<<(phi.pi[i]));
    return ans;
}

vector<int> automorphism_outmap(automorphism &phi, vector<int> &outmap)
{
    /**
     * The image of an outmap under an automorphism phi.
     */

    vector<int> ans((1<<N));
    for (int i=0; i<(1<<N); i++)
        ans[automorphism_point(phi, i)] = automorphism_point(phi, outmap[i]^phi.A);
    return ans;
}

history automorphism_history(automorphism &phi, history &H, int initial_index = 0)
{
    /**
     * The image of an history H under an automorphism phi.
     */

    history ans;
    ans.points.resize(H.points.size());
    ans.values.resize(H.values.size());
    for (int i=initial_index; i<H.points.size(); i++){
        ans.points[i] = automorphism_point(phi, H.points[i]);
        ans.values[i] = automorphism_point(phi, H.values[i]^phi.A);
    }
    return ans;
}

sequence automorphism_sequence(automorphism &phi, sequence &S)
{
    /**
     * The image of a sequence S under an automorphism phi.
     */

    sequence ans;
    ans.points.resize(S.points.size());
    ans.values.resize(S.values.size());
    for (int i=0; i<S.points.size(); i++){
        ans.points[i] = automorphism_point(phi, S.points[i]);
        ans.values[i] = automorphism_point(phi, S.values[i]^phi.A);
    }
    ans.next_point = automorphism_point(phi, S.next_point);
    return ans;
}

bool is_history_fixed(automorphism &phi, history &H)
{
    /**
     * Determines whether an automorphism phi fixes a history H.
     */

    for (int i=0; i<H.points.size(); i++)
        if (H.points[i] != automorphism_point(phi, H.points[i]) || H.values[i] != automorphism_point(phi, H.values[i]^phi.A))
            return false;
    return true;
}

vector<automorphism> subgroup_H(history &H)
{
    /**
     * Returns the subgroup of automorphisms which fixes a history H.
     */

    vector<automorphism> ans;
    for (auto phi: all_automorphisms)
        if (is_history_fixed(phi, H))
            ans.push_back(phi);
    return ans;
}

unordered_set<int> orbit_history(int X, vector<automorphism> &sub_H)
{
    /**
     * Returns the orbit of a point X according to a subset of automorphism sub_H.
     */

    unordered_set<int> ans;
    for (auto phi: sub_H)
        ans.insert(automorphism_point(phi, X));
    return ans;
}

bool is_outmap_fixed(automorphism &phi, vector<int> &outmap)
{
    /**
     * Determines whether an automorphism phi fixes an outmap.
     */

    for (int i=0; i<(1<<N); i++)
        if (outmap[automorphism_point(phi, i)] != automorphism_point(phi, outmap[i]^phi.A))
            return false;
    return true;
}

int size_stabilizer_outmap(vector<int> &outmap)
{
    /**
     * Returns the number of automorphisms which fix a given orientation.
     */

    int fixed = 0;
    for (auto phi: all_automorphisms)
        if (is_outmap_fixed(phi, outmap))
            fixed ++;
    return fixed;
}

bool similar_history(history &H1, history &H2, vector<automorphism> &sub_H)
{
    /**
     * Determines whether two histories are isomorphic to each other.
     * It assumes that H1 and H2 only differ in the last point, and that sub_H is the subgroup of automorphisms which fix the initial points common to H1 and H2.
     * It assumes that the last points of H1 and H2 are either the same or in different orbits (which implies they are not isomorphic).
     */

    if (H1.points.back() != H2.points.back())
        return false;
    for (auto phi: sub_H)
        if (automorphism_point(phi, H1.values.back()^phi.A) == H2.values.back())
            return true;
    return false;
}

bool good_history(history &H)
{
    /**
     * Determines whether H is a history.
     */

    for (int i=0; i<H.points.size(); i++) for (int j=0; j<i; j++)
        if (((H.points[i]^H.points[j])&(H.values[i]^H.values[j])) == 0)
            return 0;
    for (auto w: H.values)
        if (w == 0)
            return 0;
    return 1;
}

bool good_sequence(sequence &S)
{
    /**
     * Determines whether S is a sequence.
     */

    for (int i=0; i<S.points.size(); i++) for (int j=0; j<i; j++)
        if (((S.points[i]^S.points[j])&(S.values[i]^S.values[j])) == 0)
            return 0;
    for (auto w: S.values)
        if (w == 0)
            return 0;
    for (auto u: S.points)
        if (u == S.next_point)
            return 0;
    return 1;
}

sequence sigma(history &H)
{
    /**
     * Returns the sequence leading to a given history H.
     */

    sequence ans;
    ans.points = H.points;
    ans.values = H.values;
    ans.next_point = ans.points.back();
    ans.points.pop_back();
    ans.values.pop_back();
    return ans;
}

bool compatible(history &H, vector<int> &outmap)
{
    /**
     * Determines whether a given history H is compatible with a given outmap.
     */

    for (int i=0; i<H.points.size(); i++)
        if (H.values[i] != outmap[H.points[i]])
            return false;
    return true;
}

bool end_sequence(sequence &S, vector<int> &outmap)
{
    /**
     * Determines whether the last point of a sequence S will cause a clash or a sink according to an outmap.
     */

    if (outmap[S.next_point] == 0)
        return true;
    for (int i=0; i<S.points.size(); i++)
        if (((S.values[i]^outmap[S.next_point])&(S.points[i]^S.next_point)) == 0)
            return true;
    return false;
}

void traverse(history H, int m)
{
    /**
     * Traverses through all histories and sequences up to automorphism.
     * Determines the value of the payoff function, multiplied by the number of automorphism (to ensure they are integers).
     * m determines the number of branches that have been condensed together by the automorphisms.
     */

    all_histories_symmetry.push_back(H); // a new possible history
    vector<history> children = {}; // a vector of histories that can appear after H.
    vector<int> orbits = {}; // a vector of representatives for each orbit of non-queried points, according to the automorphisms which fix H.
    bool used[1<<N] = {};
    vector<automorphism> sub_H = subgroup_H(H);
    for (auto i: H.points)
        used[i] = 1;
    for (int i=0; i<(1<<N); i++) if (!used[i]){
        for (auto j: orbit_history(i, sub_H))
            used[j] = 1;
        orbits.push_back(i);
    }
    history H_next = H;
    H_next.points.push_back(-1);
    H_next.values.push_back(-1);
    sequence sigma;
    sigma.points = H.points;
    sigma.values = H.values;
    for (auto X: orbits){
        H_next.points[H_next.points.size()-1] = X;
        bool good = 0;
        for (int val=1; val<(1<<N); val++){
            bool fail = 0;
            for (int i=0; i<H_next.values.size()-1; i++){
                if (((H_next.values[i]^val)&(H_next.points[i]^X)) == 0){
                    fail = 1;
                    break;
                }
            }
            if (!fail){ // finds all possible next histories, up to automorphism of the next chosen point
                H_next.values[H_next.values.size()-1] = val;
                children.push_back(H_next);
                good = 1;
            }
        }
        if (!good && must_pick_this_one.size() < all_histories_symmetry.size()){
            // if a given point has no possible value for a given history, the first player can pick it and finish the game
            must_pick_this_one.push_back(X);
        }
    }
    if (must_pick_this_one.size() < all_histories_symmetry.size())
        must_pick_this_one.push_back(-1); // in case all points have possible values
    for (auto X: orbits){
        if (must_pick_this_one.back() != -1 && must_pick_this_one.back() != X) // if the main player necessarily picks another point
            continue;
        H_next.points[H_next.points.size()-1] = X;
        sigma.next_point = X;
        int sigma_id = all_sequences_symmetry.size();
        all_sequences_symmetry.push_back(sigma); // a new possible sequence
        if (H.points.size() > 0){
            // generates all outmaps which agree with H_next
            vector<vector<int>> possible_outmaps = {{}};
            possible_outmaps[0].resize(1<<N);
            fill(possible_outmaps[0].begin(), possible_outmaps[0].end(), -1);
            for (int i=0; i<H.points.size(); i++)
                possible_outmaps[0][H.points[i]] = H.values[i];
            for (int i=0; i<(1<<N); i++){
                if (possible_outmaps[0][i] != -1)
                    continue;
                vector<vector<int>> next_possible_outmaps = {};
                if (i == X){
                    for (auto each: possible_outmaps){
                        each[i] = 0;
                        next_possible_outmaps.push_back(each);
                        for (int j=1; j<(1<<N); j++){
                            bool fail = 0;
                            for (int k=0; k<H.points.size(); k++){
                                if (((H.values[k]^j)&(H.points[k]^i)) == 0){
                                    fail = 1;
                                    break;
                                }
                            }
                            if (fail){
                                each[i] = j;
                                next_possible_outmaps.push_back(each);
                            }
                        }
                    }
                }
                else{
                    for (auto each: possible_outmaps){
                        for (int j=0; j<(1<<N); j++){
                            each[i] = j;
                            next_possible_outmaps.push_back(each);
                        }
                    }
                }
                swap(possible_outmaps, next_possible_outmaps);
            }
            for (auto outmap: possible_outmaps){ // given a payoff and an outmap, updates the payoff accordingly, taking the automorphisms into consideration
                int outmap_id = best_outmap[outmap_to_int(outmap)];
                payoff[outmap_id][sigma_id] =
                        payoff[outmap_id][sigma_id] +
                        m*(H.points.size() + 1) * stabilizer[outmap_id];
            }
        }
        else{
            for (auto outmap: all_outmaps){ // given a payoff and an outmap, updates the payoff accordingly, taking the automorphisms into consideration
                int outmap_id = best_outmap[outmap_to_int(outmap)];
                if (compatible(H, outmap) && end_sequence(sigma, outmap))
                    payoff[outmap_id][sigma_id] =
                        payoff[outmap_id][sigma_id] +
                        m*(H.points.size() + 1)*stabilizer[outmap_id];
            }
        }
    }
    if (must_pick_this_one.back() != -1) // if this is the end of the branch
        return;
    vector<pair<history, int>> orbits_history = {}; // a vector of the next possible histories, and how many there are up to automorphism
    for (auto child: children){
        bool found = false;
        for (int i=0; i<orbits_history.size(); i++){
            if (similar_history(orbits_history[i].first, child, sub_H)){
                orbits_history[i].second ++;
                found = true;
                break;
            }
        }
        if (!found)
            orbits_history.push_back(make_pair(child, 1));
    }
    for (auto orbit: orbits_history) // traverse to the new histories
        traverse(orbit.first, m * orbit.second);
}

int main()
{
    vector<int> id;
    for (int i=0; i<N; i++)
        id.push_back(i);
    do{ // creates all automorphisms
        for (int i=0; i<(1<<N); i++){
            automorphism phi;
            phi.A = i;
            phi.pi = id;
            all_automorphisms.push_back(phi);
        }
    }while(next_permutation(id.begin(), id.end()));

    all_outmaps[0].resize(1<<N);
    for (int i=0; i<(1<<N); i++){ // creates all outmaps
        vector<vector<int>> next_all_outmaps;
        for (auto u: all_outmaps){
            for (int j=0; j<(1<<N); j++){
                u[i] = j;
                next_all_outmaps.push_back(u);
            }
        }
        swap(all_outmaps, next_all_outmaps);
    }

    for (auto outmap: all_outmaps){
        int fixed = 0;
        vector<int> best = outmap; // the smallest outmap isomorphic to the original outmap, which will be the representative of its orbit
        for (auto phi: all_automorphisms){
            auto x = automorphism_outmap(phi, outmap);
            if (x == outmap)
                fixed ++;
            else
                best = min(best, x);
        }
        if (best == outmap){
            best_outmap[outmap_to_int(outmap)] = all_outmaps_symmetry.size();
            stabilizer.push_back(fixed);
            all_outmaps_symmetry.push_back(outmap);
        }
        else
            best_outmap[outmap_to_int(outmap)] = best_outmap[outmap_to_int(best)];
    }

    payoff.resize(all_outmaps_symmetry.size());
    history H;
    traverse(H, 1); // find all histories and sequences up to automorphism, and update the payoff function

    for (int outmap_id=0; outmap_id<all_outmaps_symmetry.size(); outmap_id++){
        // creates the inequality constraints for each outmap
        bool first = 1;
        string constraint;
        for (auto each: payoff[outmap_id]){
            if (!first){
                constraint += " + ";
            }
            first = 0;
            sequence S = all_sequences_symmetry[each.first];
            constraint += to_string(each.second) + " " + representation(S);
        }
        if (!first){
            constraint += " - " + to_string(all_automorphisms.size()) + " v <= 0";
            constraints.push_back(constraint);
        }
    }

    for (int h=0; h<all_histories_symmetry.size(); h++){
        // creates the equality constraints for each history
        history H = all_histories_symmetry[h];
        if (H.points.empty())
            continue;
        bool first = 1;
        vector<int> orbits; // creates the same orbits of next points as in traverse
        if (must_pick_this_one[h] == -1){
            bool used[1<<N] = {};
            vector<automorphism> sub_H = subgroup_H(H);
            for (auto i: H.points)
                used[i] = 1;
            for (int i=0; i<(1<<N); i++) if (!used[i]){
                for (auto j: orbit_history(i, sub_H))
                    used[j] = 1;
                orbits.push_back(i);
            }
        }
        else
            orbits = {must_pick_this_one[h]};
        sequence S;
        S.points = H.points;
        S.values = H.values;
        string constraint;
        for (auto u: orbits){ // adds all the next histories
            if (!first){
                constraint += " + ";
            }
            first = 0;
            S.next_point = u;
            constraint += representation(S);
        }
        S = sigma(H);
        constraint += " - " + representation(S) + " = 0";
        constraints.push_back(constraint);
    }

    // the constraint that the probability of picking an initial vertex is 1
    sequence one;
    one.next_point = 0;
    constraints.push_back(representation(one) + " = 1");

    // writing the result to a .lp file
    writeFileLP("LinearProgram.lp", constraints);

    return 0;
}
