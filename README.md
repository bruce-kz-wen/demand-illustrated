# Nonparametric demand, illustrated

**Live site: https://bruce-kz-wen.github.io/demand-illustrated/**

Interactive illustrations of the estimator in "Fully Flexible Nonparametric Estimation of Demand in High Dimensions".

The first tab is about the Matryoshka basis. Type a function of a product's index and price and watch the pieces of the dictionary rebuild it, with the error after each piece. It then compares the dictionary with the full tensor-product grid, with two inputs and with up to one hundred.

## Running it locally

The site is static and has no build step. Open `index.html` in a browser, or serve the folder:

```
python3 -m http.server
```

## Files

| Path | What it holds |
|---|---|
| `index.html` | the page |
| `css/style.css` | layout, and the light and dark themes |
| `js/core.js` | the numerics: the dictionary, its ordering, projections, and the demand system |
| `js/matryoshka.js` | the Matryoshka tab |
| `js/viz.js` | charts and shared helpers |
| `js/mathexpr.js` | the parser for typed functions |
| `vendor/katex/` | [KaTeX](https://katex.org) 0.19.1 for the formulas (MIT license) |
