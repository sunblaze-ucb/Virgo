#include <cstdio>
#include <vector>
#include <cstdlib>

int n, t;
int N, T;

const int add_gate = 0, mult_gate = 1, input_gate = 3, relay = 10, minus_gate = 7;
const int mult_omega = 14;
const int direct_relay = 4;

class gate
{
public:
    int type;
    long long id;
    long long ch[2];
};

class circuit
{
public:
    std::vector<std::vector<gate> > layers;

    void output(const char *path, const char *meta_path)
    {
        FILE *f = fopen(path, "w");

        fprintf(f, "%d\n", (int)layers.size());
        for(int i = 0; i < layers.size(); ++i)
        {
            fprintf(f, "%d", (int)layers[i].size());
            for(int j = 0; j < layers[i].size(); ++j)
            {
                gate &g = layers[i][j];
                fprintf(f, " %d %lld %lld %lld", g.type, g.id, g.ch[0], g.ch[1]);
            }
            fprintf(f, "\n");
        }
        fclose(f);

        FILE *meta = fopen(meta_path, "w");

        for(int i = 0; i < layers.size(); ++i)
        {
            fprintf(meta, "0 0 0 0 0\n");
        }
        fclose(meta);
    }
};

circuit C;

std::vector<long long> poly_coef;

int main(int argc, char* argv[])
{
    if(argc != 3)
    {
        printf("./build_fft_circuit #log_verifiers #log_degree\n");
    }
    sscanf(argv[1], "%d", &n);
    sscanf(argv[2], "%d", &t);
    N = 1 << n, T = 1 << t;

    poly_coef.resize(T);
    for(int i = 0; i < poly_coef.size(); ++i)
        poly_coef[i] = rand() % (1000000007);
    
    //input layer
    C.layers.push_back(std::vector<gate>());
    for(int i = 0; i < T; ++i)
    {
        gate g;
        g.type = input_gate;
        g.id = i;
        g.ch[0] = poly_coef[i];
        g.ch[1] = poly_coef[i];
        C.layers[0].push_back(g);
    }

    //relay layer
    int blk_sz = N / T;
    C.layers.push_back(std::vector<gate>());
    for(int i = 0; i < blk_sz; ++i)
    {
        for(int j = 0; j < T; ++j)
        {
            gate g;
            g.id = i * T + j;
            g.type = relay;
            g.ch[0] = j;
            g.ch[1] = 0;
            C.layers[1].push_back(g);
        }
    }

    long long rot_mul[62];
    rot_mul[0] = 1;
    for(int i = 1; i < 62; ++i)
        rot_mul[i] = rot_mul[i - 1] + rot_mul[i - 1];
    std::vector<long long> x_arr;
    x_arr.resize(N);
    //fft layers
    for(int dep = t - 1; dep >= 0; --dep)
    {
        C.layers.push_back(std::vector<gate>());
        C.layers.push_back(std::vector<gate>());
        int lst_layer = C.layers.size() - 1;
        int lst2_layer = lst_layer - 1;
        C.layers[lst2_layer].resize(N);
        C.layers[lst_layer].resize(N);
        int blk_size = 1 << (n - dep);
        int half_blk_size = blk_size / 2;
        
        x_arr[0] = 0;
        for(int j = 1; j < blk_size; ++j)
            x_arr[j] = x_arr[j - 1] + rot_mul[dep];
        
        int cnt = 0;
        for(int k = 0; k < (blk_size / 2); ++k)
        {
            int double_k = k & (half_blk_size - 1);
            for(int j = 0; j < (1 << dep); ++j)
            {
                gate g[2];
                g[0].type = relay;
                g[0].id = cnt;
                g[0].ch[0] = double_k << (dep + 1) | j;
                g[0].ch[1] = 0;
                C.layers[lst2_layer][cnt] = g[0];
                g[1].type = mult_omega;
                g[1].id = cnt + 1;
                g[1].ch[0] = double_k << (dep + 1) | (1 << dep) | j;
                g[1].ch[1] = x_arr[k];
                C.layers[lst2_layer][cnt + 1] = g[1];

                g[0].type = add_gate;
                g[0].id = k << dep | j;
                g[0].ch[0] = cnt;
                g[0].ch[1] = cnt + 1;

                g[1].type = minus_gate;
                g[1].id = (k + blk_size / 2) << dep | j;
                g[1].ch[0] = cnt;
                g[1].ch[1] = cnt + 1;
                C.layers[lst_layer][k << dep | j] = g[0];
                C.layers[lst_layer][(k + blk_size / 2) << dep | j] = g[1];

                cnt += 2;
            }
        }
    }

    //final reply gate

    C.layers.push_back(std::vector<gate>());
    int last_layer = C.layers.size() - 1;
    C.layers[last_layer].resize(N);

    for(int i = 0; i < N; ++i)
    {
        gate g;
        g.type = direct_relay;
        g.id = i;
        g.ch[0] = i;
        g.ch[1] = 0;
        C.layers[last_layer][i] = g;
    }

    C.output("fft.txt", "fft_meta.txt");
    
    return 0;
}