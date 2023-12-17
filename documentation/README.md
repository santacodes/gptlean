# Docsify Template

> A simple [Docsify](https://github.com/docsifyjs/docsify/) template for creating Markdown-based documentation sites, with no build process required.

## Site Setup

### Static Webserver

Upload these template files to any static web server. The file `.nojekyll` is only required if hosting the site on GitHub Pages and otherwise can be removed.

## Computational Complexity Classes

#### BPP

A language L is in BPP if and only if there exits a probabilistic Turing machine M,such that

- M runs for polynomial time on all inputs
- For all x in L,M outputs 1 with probability greater than or equal to 2/3
- For all x not in L,M outputs 1 with probability less than or equal to 1/3

```lean4
def in_bpp (A : set string) : Prop :=
  ∃ (M : string → bool),
    turing_machine M ∧ ∀ x ∈ A, M x = tt ∧ M.prob_accept ≥ 2/3
    ∧ ∀ x ∉ A, M x = ff ∧ M.prob_accept ≤ 1/3

end bpp

```

#### PSPACE

In computational complexity theory, PSPACE is the set of all decision problems that can be solved by a Turing machine using a polynomial amount of space.
If we denote by SPACE(f(n)), the set of all problems that can be solved by Turing machines using O(f(n)) space for some function f of the input size n, then we can define PSPACE formally as

![img](https://i.ibb.co/v1H6J9g/pspace.png)

PSPACE is a strict superset of the set of context-sensitive languages

```
def PSPACE (TM  TuringMachine) (f : TMConfiguration TM → bool) :=
  ∃ (poly  ℕ :ℕ), ∀ (n  ℕ), ∃ (config : TMConfiguration TM),
    config.tape.length ≤ poly n ∧
    (∀ (eps  ℝ), eps  0 → ∃ (k ℕ), Pr[f TM config k] ≥ 1 - eps)

end complexity
```

#### Hosting Site

To host this template on GitHub Pages do the following:

1. Log into GitHub if you have not done so already
2. Tap the **Use this template** button in the upper-right of this GitHub Repository and choose **Create a new repository**
3. Enter a name for your new Repository and then tap the **Create repository** button
4. Once your new Repostitory is created go to **Settings**, then select **Pages** from the left-hand sidebar, and under **Branch** choose **main** and then tap the **Save** button
5. Wait a minute or two and refresh the same **Pages** page - once your site is ready a message will be displayed at the top of the screen along with a site link and a **Visit site** button

#### Editing Content

How about editing the content of your new Docsify site on GitHub Pages? View the Markdown page you want to edit (for example, **README.md**) and tap the **Pencil Icon**, then save any changes by tapping the green **Commit changes...** button. In just a few moments the Docsify site will be automatically updated to reflect those changes.

### Viewing Locally

Run `npx serve .` (Node.js users) or `python -m http.server 8000` (Python users) in the repo folder to serve run locally.

## Docsify Documentation

To learn more about using Docsify, visit https://docsify.js.org.

```

```
